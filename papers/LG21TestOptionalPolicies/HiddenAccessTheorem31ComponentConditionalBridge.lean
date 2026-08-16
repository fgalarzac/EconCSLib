import LG21TestOptionalPolicies.HiddenAccessTheorem31NoReportMixtureBridge
import LG21TestOptionalPolicies.FullProfileGaussianSequentialBridge
import LG21TestOptionalPolicies.SelectedSignalPosteriorBridge

/-!
# Literal component conditional laws for LG21 Theorem 3.1

This module keeps the two source components of the actual hidden-access
`X = 0` population separate long enough to derive their conditional skill
laws from the population measure and the timed reporting action.  It does not
choose a cutoff, a pointwise PBO version, or an equilibrium replacement.

The no-access component is transported to the literal full non-test
base/skill source law.  The access-withhold component is the normalized
restriction defined by the actual post-score reporting action; its conditional
law is consequently a score-then-skill disintegration of that selected source
measure.  Both conditional-law conclusions are almost everywhere statements.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-! ## The literal no-access component -/

/-- The actual source law conditional on no test access. -/
def lg21HiddenAccessNoAccessLaw
    {Feature : Type*} [Fintype Feature]
    (M : LG21ContinuousGaussianPopulation Feature) :
    Measure (Bool × (ℝ × (Feature → ℝ))) :=
  lg21NormalizedRestriction (lg21ContinuousGaussianPopulationLaw M)
    (lg21HiddenAccessNoAccessEvent (Feature := Feature))

theorem lg21HiddenAccessNoAccessLaw_isProbability
    {Feature : Type*} [Fintype Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false}) :
    IsProbabilityMeasure (lg21HiddenAccessNoAccessLaw M) := by
  letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
  letI : IsProbabilityMeasure (lg21ContinuousGaussianNoiseLaw M) := by
    unfold lg21ContinuousGaussianNoiseLaw
    infer_instance
  letI : IsProbabilityMeasure
      (lg21ContinuousGaussianStudentPrimitiveLaw M) := by
    unfold lg21ContinuousGaussianStudentPrimitiveLaw
    infer_instance
  letI : IsProbabilityMeasure (lg21ContinuousGaussianPopulationLaw M) :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  apply lg21NormalizedRestriction_isProbability
  · change lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessNoAccessEvent (Feature := Feature)) ≠ 0
    rw [show lg21HiddenAccessNoAccessEvent (Feature := Feature) =
        ({false} : Set Bool) ×ˢ Set.univ by
          ext student
          change student.1 = false ↔ student.1 = false ∧ student.2 ∈ Set.univ
          simp,
      lg21ContinuousGaussianPopulation_access_student_factorization]
    rw [IsProbabilityMeasure.measure_univ, mul_one]
    exact ne_of_gt hnoAccess
  · exact measure_ne_top _ _

/-- Conditioning the literal product population on `Z = 0` leaves the
student primitive block unchanged. -/
theorem lg21HiddenAccessNoAccessLaw_map_student_eq
    {Feature : Type*} [Fintype Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false}) :
    (lg21HiddenAccessNoAccessLaw M).map Prod.snd =
      lg21ContinuousGaussianStudentPrimitiveLaw M := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let studentLaw := lg21ContinuousGaussianStudentPrimitiveLaw M
  let noAccessEvent : Set (Bool × (ℝ × (Feature → ℝ))) :=
    lg21HiddenAccessNoAccessEvent (Feature := Feature)
  have hraw_probability : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsProbabilityMeasure rawLaw := hraw_probability
  letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
  have hstudent_probability : IsProbabilityMeasure studentLaw := by
    unfold studentLaw lg21ContinuousGaussianStudentPrimitiveLaw
    unfold lg21ContinuousGaussianNoiseLaw
    infer_instance
  letI : IsProbabilityMeasure studentLaw := hstudent_probability
  have hnoAccessEvent : noAccessEvent = ({false} : Set Bool) ×ˢ Set.univ := by
    ext student
    change student.1 = false ↔ student.1 = false ∧ student.2 ∈ Set.univ
    simp
  have hraw_noAccess : rawLaw noAccessEvent = M.accessLaw {false} := by
    rw [hnoAccessEvent, lg21ContinuousGaussianPopulation_access_student_factorization]
    simp [studentLaw]
  ext target htarget
  rw [Measure.map_apply (measurable_snd) htarget]
  change lg21NormalizedRestriction rawLaw noAccessEvent (Prod.snd ⁻¹' target) =
    studentLaw target
  rw [lg21NormalizedRestriction_apply rawLaw (measurable_snd htarget)]
  have hpreimage :
      Prod.snd ⁻¹' target ∩ noAccessEvent = ({false} : Set Bool) ×ˢ target := by
    rw [hnoAccessEvent]
    ext student
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod,
      Set.mem_singleton_iff, Set.mem_univ, and_true]
    constructor <;> intro h
    · exact ⟨h.2, h.1⟩
    · exact ⟨h.2, h.1⟩
  rw [hpreimage]
  rw [show rawLaw = lg21ContinuousGaussianPopulationLaw M by rfl,
    lg21ContinuousGaussianPopulation_access_student_factorization]
  rw [hraw_noAccess]
  rw [← mul_assoc, ENNReal.inv_mul_cancel (ne_of_gt hnoAccess)
    (measure_ne_top _ _), one_mul]

/-- The full literal primitive profile on the no-access component has the
same source law as the corresponding access component.  This is a product-law
transport, not an identification of any belief. -/
theorem lg21HiddenAccessNoAccessLaw_full_primitive_law
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature) :
    (lg21HiddenAccessNoAccessLaw M).map
      (lg21ContinuousPopulationFullPrimitive testFeature) =
      lg21ContinuousGaussianFullProfilePrimitiveLaw M testFeature := by
  let sourcePrimitiveLaw := lg21ContinuousGaussianStudentPrimitiveLaw M
  let splitPrimitive : ℝ × (Feature → ℝ) →
      ℝ × ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) :=
    fun primitive => (primitive.1,
      lg21ContinuousGaussianNoiseSplit testFeature primitive.2)
  have hsplitPrimitive : Measurable splitPrimitive := by
    exact measurable_fst.prodMk
      ((lg21ContinuousGaussianNoiseSplit testFeature).measurable.comp measurable_snd)
  letI : IsProbabilityMeasure (lg21ContinuousGaussianNoiseLaw M) := by
    unfold lg21ContinuousGaussianNoiseLaw
    infer_instance
  have hprimitive : sourcePrimitiveLaw.map splitPrimitive =
      lg21ContinuousGaussianFullProfilePrimitiveLaw M testFeature := by
    change Measure.map (Prod.map id (lg21ContinuousGaussianNoiseSplit testFeature))
      ((gaussianReal M.priorMean M.priorVariance).prod
        (lg21ContinuousGaussianNoiseLaw M)) = _
    rw [← Measure.map_prod_map (gaussianReal M.priorMean M.priorVariance)
      (lg21ContinuousGaussianNoiseLaw M) measurable_id
      (lg21ContinuousGaussianNoiseSplit testFeature).measurable]
    rw [lg21ContinuousGaussianNoiseLaw_map_nonTest_test_eq]
    simp [lg21ContinuousGaussianFullProfilePrimitiveLaw]
  calc
    (lg21HiddenAccessNoAccessLaw M).map
        (lg21ContinuousPopulationFullPrimitive testFeature) =
      ((lg21HiddenAccessNoAccessLaw M).map Prod.snd).map splitPrimitive := by
        rw [Measure.map_map hsplitPrimitive measurable_snd]
        rfl
    _ = sourcePrimitiveLaw.map splitPrimitive := by
      rw [lg21HiddenAccessNoAccessLaw_map_student_eq M hnoAccess]
    _ = lg21ContinuousGaussianFullProfilePrimitiveLaw M testFeature := hprimitive

/-- Drop the designated test-noise coordinate from the full primitive source
profile and retain exactly the `(non-test base, skill)` observation. -/
def lg21HiddenAccessFullPrimitiveBaseSkillObservation
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) :
    ℝ × ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) →
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ :=
  fun primitive =>
    ((fun feature => primitive.1 + primitive.2.1 feature), primitive.1)

theorem lg21HiddenAccessFullPrimitiveBaseSkillObservation_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) :
    Measurable
      (lg21HiddenAccessFullPrimitiveBaseSkillObservation (Feature := Feature)
        testFeature) := by
  exact (measurable_pi_lambda _ fun feature =>
    measurable_fst.add
      ((measurable_pi_apply feature).comp (measurable_fst.comp measurable_snd))).prodMk
        measurable_fst

/-- The full primitive source law loses no information relevant to the
no-access base/skill component when the independent test-noise coordinate is
discarded. -/
theorem lg21ContinuousGaussianFullProfilePrimitiveLaw_map_base_skill_eq
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature) :
    (lg21ContinuousGaussianFullProfilePrimitiveLaw M testFeature).map
        (lg21HiddenAccessFullPrimitiveBaseSkillObservation testFeature) =
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature := by
  let prior : Measure ℝ := gaussianReal M.priorMean M.priorVariance
  let nonTestNoise : Measure (LG21NonTestFeature Feature testFeature → ℝ) :=
    lg21ContinuousGaussianNonTestNoiseLaw M testFeature
  let testNoise : Measure ℝ := gaussianReal 0 (M.noiseVariance testFeature)
  let baseMap : ℝ × (LG21NonTestFeature Feature testFeature → ℝ) →
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ :=
    fun primitive =>
      ((fun feature => primitive.1 + primitive.2 feature), primitive.1)
  let fullMap : ℝ × ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) →
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ :=
    lg21HiddenAccessFullPrimitiveBaseSkillObservation testFeature
  have hbaseMap : Measurable baseMap := by
    exact (measurable_pi_lambda _ fun feature =>
      measurable_fst.add ((measurable_pi_apply feature).comp measurable_snd)).prodMk
        measurable_fst
  have hfullMap : Measurable fullMap := by
    exact lg21HiddenAccessFullPrimitiveBaseSkillObservation_measurable testFeature
  letI : IsProbabilityMeasure prior := by
    dsimp [prior]
    infer_instance
  letI : IsProbabilityMeasure nonTestNoise := by
    dsimp [nonTestNoise, lg21ContinuousGaussianNonTestNoiseLaw]
    infer_instance
  letI : IsProbabilityMeasure testNoise := by
    dsimp [testNoise]
    infer_instance
  change (prior.prod (nonTestNoise.prod testNoise)).map fullMap =
    (prior.prod nonTestNoise).map baseMap
  calc
    (prior.prod (nonTestNoise.prod testNoise)).map fullMap =
        (((prior.prod nonTestNoise).prod testNoise).map
          MeasurableEquiv.prodAssoc).map fullMap := by
          rw [Measure.prodAssoc_prod]
    _ = ((prior.prod nonTestNoise).prod testNoise).map
        (fullMap ∘ MeasurableEquiv.prodAssoc) := by
          rw [Measure.map_map hfullMap MeasurableEquiv.prodAssoc.measurable]
    _ = ((prior.prod nonTestNoise).prod testNoise).map
        (baseMap ∘ Prod.fst) := by
          rfl
    _ = (((prior.prod nonTestNoise).prod testNoise).map Prod.fst).map baseMap := by
          rw [Measure.map_map hbaseMap measurable_fst]
    _ = (prior.prod nonTestNoise).map baseMap := by
          rw [Measure.map_fst_prod]
          simp

/-- The literal no-access component maps exactly to the displayed full
non-test base/skill source law. -/
theorem lg21HiddenAccessNoAccessLaw_base_skill_law
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature) :
    (lg21HiddenAccessNoAccessLaw M).map
        (lg21HiddenAccessBaseSkillObservation testFeature) =
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature := by
  let fullPrimitive := lg21ContinuousPopulationFullPrimitive testFeature
  let fullBaseSkill :=
    lg21HiddenAccessFullPrimitiveBaseSkillObservation testFeature
  have hfullPrimitive : Measurable fullPrimitive := by
    exact (measurable_fst.comp measurable_snd).prodMk
      ((measurable_pi_lambda _ fun feature =>
        (measurable_pi_apply feature.1).comp (measurable_snd.comp measurable_snd)).prodMk
          ((measurable_pi_apply testFeature).comp
            (measurable_snd.comp measurable_snd)))
  have hfullBaseSkill : Measurable fullBaseSkill := by
    exact lg21HiddenAccessFullPrimitiveBaseSkillObservation_measurable testFeature
  calc
    (lg21HiddenAccessNoAccessLaw M).map
        (lg21HiddenAccessBaseSkillObservation testFeature) =
      ((lg21HiddenAccessNoAccessLaw M).map fullPrimitive).map fullBaseSkill := by
        rw [Measure.map_map hfullBaseSkill hfullPrimitive]
        rfl
    _ = (lg21ContinuousGaussianFullProfilePrimitiveLaw M testFeature).map
        fullBaseSkill := by
          rw [lg21HiddenAccessNoAccessLaw_full_primitive_law M hnoAccess testFeature]
    _ = lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature := by
          exact lg21ContinuousGaussianFullProfilePrimitiveLaw_map_base_skill_eq
            M testFeature

/-- The displayed full non-test base/skill source law is a probability law. -/
theorem lg21ContinuousGaussianFullBaseLatentPrimitiveLaw_isProbability
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature) :
    IsProbabilityMeasure
      (lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature) := by
  letI : IsProbabilityMeasure (gaussianReal M.priorMean M.priorVariance) := by
    infer_instance
  letI : IsProbabilityMeasure
      (lg21ContinuousGaussianNonTestNoiseLaw M testFeature) := by
    unfold lg21ContinuousGaussianNonTestNoiseLaw
    infer_instance
  apply Measure.isProbabilityMeasure_map
  exact ((measurable_pi_lambda _ fun feature =>
    measurable_fst.add ((measurable_pi_apply feature).comp measurable_snd)).prodMk
      measurable_fst).aemeasurable

/-! ## Actual source conditional kernels -/

/-- The conditional skill kernel on the literal no-access component is the
regular conditional distribution of the explicit full non-test base/skill
source law.  No value is asserted outside the component's base marginal. -/
theorem lg21HiddenAccessNoAccessLaw_condDistrib_skill_base_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature) :
    let law := lg21HiddenAccessNoAccessLaw M
    let primitiveLaw := lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature
    let base : Bool × (ℝ × (Feature → ℝ)) →
        (LG21NonTestFeature Feature testFeature → ℝ) :=
      fun student => lg21HiddenAccessStudentBase testFeature student.2
    let skill : Bool × (ℝ × (Feature → ℝ)) → ℝ :=
      lg21ContinuousPopulationSkill
    letI : IsProbabilityMeasure law :=
      lg21HiddenAccessNoAccessLaw_isProbability M hnoAccess
    letI : IsFiniteMeasure law := ⟨by simp⟩
    letI : IsProbabilityMeasure primitiveLaw := by
      exact lg21ContinuousGaussianFullBaseLatentPrimitiveLaw_isProbability M testFeature
    letI : IsFiniteMeasure primitiveLaw := ⟨by simp⟩
    condDistrib skill base law =ᵐ[law.map base]
      condDistrib Prod.snd Prod.fst primitiveLaw := by
  intro law primitiveLaw base skill
  letI : IsProbabilityMeasure law :=
    lg21HiddenAccessNoAccessLaw_isProbability M hnoAccess
  letI : IsFiniteMeasure law := ⟨by simp⟩
  letI : IsProbabilityMeasure primitiveLaw := by
    dsimp [primitiveLaw]
    exact lg21ContinuousGaussianFullBaseLatentPrimitiveLaw_isProbability M testFeature
  letI : IsFiniteMeasure primitiveLaw := ⟨by simp⟩
  have hbase : Measurable base := by
    exact (lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd
  have hskill : Measurable skill := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  have hpair : law.map (fun student => (base student, skill student)) =
      primitiveLaw := by
    simpa [law, primitiveLaw, base, skill] using
      (lg21HiddenAccessNoAccessLaw_base_skill_law M hnoAccess testFeature)
  have hbaseMarginal : law.map base = primitiveLaw.map Prod.fst := by
    calc
      law.map base = (law.map (fun student => (base student, skill student))).map
          Prod.fst := by
            rw [Measure.map_map measurable_fst (hbase.prodMk hskill)]
            rfl
      _ = primitiveLaw.map Prod.fst := by rw [hpair]
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hbase hskill
  calc
    law.map (fun student => (base student, skill student)) = primitiveLaw := hpair
    _ = primitiveLaw.map Prod.fst ⊗ₘ
        condDistrib Prod.snd Prod.fst primitiveLaw := by
          rw [compProd_map_condDistrib measurable_snd.aemeasurable]
          change primitiveLaw = Measure.map id primitiveLaw
          exact Measure.map_id.symm
    _ = law.map base ⊗ₘ condDistrib Prod.snd Prod.fst primitiveLaw := by
          rw [hbaseMarginal]

/-! ## The literal access-and-withhold component -/

/-- The actual source law conditional on both test access and the literal
post-score decision not to report. -/
def lg21HiddenAccessAccessNoReportLaw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool) :
    Measure (Bool × (ℝ × (Feature → ℝ))) :=
  lg21NormalizedRestriction (lg21ContinuousGaussianPopulationLaw M)
    (lg21HiddenAccessAccessNoReportEvent testFeature reportDecision)

theorem lg21HiddenAccessAccessNoReportLaw_isProbability
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool)
    (hreportDecision : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ =>
      reportDecision pair.1 pair.2))
    (hpositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessAccessNoReportEvent testFeature reportDecision)) :
    IsProbabilityMeasure
      (lg21HiddenAccessAccessNoReportLaw M testFeature reportDecision) := by
  letI : IsProbabilityMeasure (lg21ContinuousGaussianPopulationLaw M) :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  apply lg21NormalizedRestriction_isProbability
  · exact ne_of_gt hpositive
  · exact measure_ne_top _ _

/-- Keep the source access coordinate alongside the full data needed to
evaluate its timed post-score reporting action. -/
def lg21HiddenAccessActionObservation
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) :
    Bool × (ℝ × (Feature → ℝ)) →
      Bool × (((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) × ℝ) :=
  fun student =>
    (lg21ContinuousPopulationAccess student,
      ((lg21HiddenAccessStudentBase testFeature student.2,
        lg21HiddenAccessStudentScore testFeature student.2),
        lg21ContinuousPopulationSkill student))

theorem lg21HiddenAccessActionObservation_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) :
    Measurable (lg21HiddenAccessActionObservation (Feature := Feature) testFeature) := by
  have hbase : Measurable (fun student : Bool × (ℝ × (Feature → ℝ)) =>
      lg21HiddenAccessStudentBase testFeature student.2) :=
    (lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd
  have hscore : Measurable (fun student : Bool × (ℝ × (Feature → ℝ)) =>
      lg21HiddenAccessStudentScore testFeature student.2) :=
    (lg21HiddenAccessStudentScore_measurable testFeature).comp measurable_snd
  have hskill : Measurable (lg21ContinuousPopulationSkill (Feature := Feature)) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  exact measurable_fst.prodMk ((hbase.prodMk hscore).prodMk hskill)

/-- The literal source event in the action-observation carrier.  It requires
access and then applies the reported post-score decision to the same base and
score coordinates; it is not an externally supplied selected cohort. -/
def lg21HiddenAccessActionWithholdEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool) :
    Set (Bool × (((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) × ℝ)) :=
  {observation |
    observation.1 = true ∧
      reportDecision observation.2.1.1 observation.2.1.2 = false}

theorem lg21HiddenAccessActionWithholdEvent_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool)
    (hreportDecision : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ =>
      reportDecision pair.1 pair.2)) :
    MeasurableSet
      (lg21HiddenAccessActionWithholdEvent testFeature reportDecision) := by
  let action : Bool × (((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) × ℝ) → Bool :=
    fun observation => reportDecision observation.2.1.1 observation.2.1.2
  have haction : Measurable action := by
    exact hreportDecision.comp
      (((measurable_fst.comp measurable_fst).comp measurable_snd).prodMk
        ((measurable_snd.comp measurable_fst).comp measurable_snd))
  change MeasurableSet
    ((Prod.fst ⁻¹' ({true} : Set Bool)) ∩
      (action ⁻¹' ({false} : Set Bool)))
  exact ((measurableSet_singleton true).preimage measurable_fst).inter
    ((measurableSet_singleton false).preimage haction)

theorem lg21HiddenAccessActionObservation_preimage_withholdEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool) :
    (lg21HiddenAccessActionObservation testFeature) ⁻¹'
        (lg21HiddenAccessActionWithholdEvent testFeature reportDecision) =
      lg21HiddenAccessAccessNoReportEvent testFeature reportDecision := by
  ext student
  rcases student with ⟨access, primitive⟩
  simp [lg21HiddenAccessActionObservation,
    lg21HiddenAccessActionWithholdEvent,
    lg21HiddenAccessAccessNoReportEvent,
    lg21HiddenAccessStudentReport, lg21HiddenAccessStudentScore,
    lg21ContinuousPopulationAccess, lg21ContinuousPopulationSkill]

/-- Pushing the selected access-withhold source law to its action observation
is exactly selection of the literal action event after mapping the full source
population. -/
theorem lg21HiddenAccessAccessNoReportLaw_map_actionObservation_eq_selected
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool)
    (hreportDecision : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ =>
      reportDecision pair.1 pair.2)) :
    (lg21HiddenAccessAccessNoReportLaw M testFeature reportDecision).map
        (lg21HiddenAccessActionObservation testFeature) =
      lg21NormalizedRestriction
        ((lg21ContinuousGaussianPopulationLaw M).map
          (lg21HiddenAccessActionObservation testFeature))
        (lg21HiddenAccessActionWithholdEvent testFeature reportDecision) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let observation := lg21HiddenAccessActionObservation testFeature
  let selected := lg21HiddenAccessActionWithholdEvent testFeature reportDecision
  have hobservation : Measurable observation :=
    lg21HiddenAccessActionObservation_measurable testFeature
  have hselected : MeasurableSet selected :=
    lg21HiddenAccessActionWithholdEvent_measurable testFeature reportDecision
      hreportDecision
  have hpreimage : observation ⁻¹' selected =
      lg21HiddenAccessAccessNoReportEvent testFeature reportDecision := by
    simpa [observation, selected] using
      (lg21HiddenAccessActionObservation_preimage_withholdEvent testFeature reportDecision)
  change (lg21NormalizedRestriction rawLaw
      (lg21HiddenAccessAccessNoReportEvent testFeature reportDecision)).map observation =
    lg21NormalizedRestriction (rawLaw.map observation) selected
  rw [← hpreimage]
  exact lg21_normalizedRestriction_map_preimage rawLaw observation hobservation selected hselected

/-- On the literal access-and-withhold source component, the base-conditioned
skill kernel is obtained by first disintegrating the actual score and then the
actual skill conditional on that `(base, score)` pair.  This does not identify
the score-conditioned kernel with an unselected Gaussian posterior. -/
theorem lg21HiddenAccessAccessNoReportLaw_condDistrib_skill_base_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool)
    (hreportDecision : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ =>
      reportDecision pair.1 pair.2))
    (hpositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessAccessNoReportEvent testFeature reportDecision)) :
    let law := lg21HiddenAccessAccessNoReportLaw M testFeature reportDecision
    let base : Bool × (ℝ × (Feature → ℝ)) →
        (LG21NonTestFeature Feature testFeature → ℝ) :=
      fun student => lg21HiddenAccessStudentBase testFeature student.2
    let score : Bool × (ℝ × (Feature → ℝ)) → ℝ :=
      fun student => lg21HiddenAccessStudentScore testFeature student.2
    let skill : Bool × (ℝ × (Feature → ℝ)) → ℝ :=
      lg21ContinuousPopulationSkill
    letI : IsProbabilityMeasure law :=
      lg21HiddenAccessAccessNoReportLaw_isProbability M testFeature reportDecision
        hreportDecision hpositive
    letI : IsFiniteMeasure law := ⟨by simp⟩
    condDistrib skill base law =ᵐ[law.map base]
      (condDistrib score base law ⊗ₖ
        condDistrib skill (fun student => (base student, score student)) law).map Prod.snd := by
  intro law base score skill
  letI : IsProbabilityMeasure law :=
    lg21HiddenAccessAccessNoReportLaw_isProbability M testFeature reportDecision
      hreportDecision hpositive
  letI : IsFiniteMeasure law := ⟨by simp⟩
  have hbase : Measurable base := by
    exact (lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd
  have hscore : Measurable score := by
    exact (lg21HiddenAccessStudentScore_measurable testFeature).comp measurable_snd
  have hskill : Measurable skill := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  let scoreSkill : Bool × (ℝ × (Feature → ℝ)) → ℝ × ℝ :=
    fun student => (score student, skill student)
  have hscoreSkill : Measurable scoreSkill := hscore.prodMk hskill
  have hchain :
      condDistrib scoreSkill base law =ᵐ[law.map base]
        condDistrib score base law ⊗ₖ
          condDistrib skill (fun student => (base student, score student)) law := by
    simpa [scoreSkill] using
      (condDistrib_score_skill_chain_ae law base score skill hbase hscore hskill)
  have hmap :
      condDistrib (Prod.snd ∘ scoreSkill) base law =ᵐ[law.map base]
        (condDistrib scoreSkill base law).map Prod.snd := by
    exact condDistrib_comp base hscoreSkill.aemeasurable measurable_snd
  filter_upwards [hmap, hchain] with observedBase hmapAt hchainAt
  change condDistrib skill base law observedBase =
    ((condDistrib score base law ⊗ₖ
      condDistrib skill (fun student => (base student, score student)) law).map Prod.snd)
        observedBase
  calc
    condDistrib skill base law observedBase =
        condDistrib (Prod.snd ∘ scoreSkill) base law observedBase := by
          rfl
    _ = (condDistrib scoreSkill base law).map Prod.snd observedBase := hmapAt
    _ = Measure.map Prod.snd (condDistrib scoreSkill base law observedBase) := by
          rw [Kernel.map_apply _ measurable_snd]
    _ = Measure.map Prod.snd
        ((condDistrib score base law ⊗ₖ
          condDistrib skill (fun student => (base student, score student)) law)
            observedBase) := by rw [hchainAt]
    _ = ((condDistrib score base law ⊗ₖ
      condDistrib skill (fun student => (base student, score student)) law).map Prod.snd)
        observedBase := by
          rw [Kernel.map_apply _ measurable_snd]

end

end LG21TestOptionalPolicies
