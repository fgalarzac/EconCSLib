import LG21TestOptionalPolicies.ContinuousPopulation
import LG21TestOptionalPolicies.ObservedAccessContinuous
import LG21TestOptionalPolicies.NestedCondDistribChain

/-!
# Literal access-conditioned population facts for LG21

The source defines access independently of the latent skill and Gaussian noise
coordinates.  This module turns that product construction into the first
observed-access law identity: conditioning the literal population on `Z = 1`
and then forgetting access recovers exactly the original student block.

It has no action, posterior, equilibrium, or conditional-kernel hypotheses.
Those remain separate obligations for the Lemma 4.1 source bridge.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory
open ProbabilityTheory
open Set

/-- The literal observed-access population, before actions are applied. -/
def lg21ContinuousGaussianAccessPopulationLaw
    {Feature : Type*} [Fintype Feature]
    (M : LG21ContinuousGaussianPopulation Feature) :
    Measure (Bool × (ℝ × (Feature → ℝ))) :=
  lg21NormalizedRestriction (lg21ContinuousGaussianPopulationLaw M)
    {student | lg21ContinuousPopulationAccess student = true}

/-- The actual non-test observed-feature index set. -/
abbrev LG21NonTestFeature (Feature : Type*) (testFeature : Feature) :=
  {feature : Feature // feature ≠ testFeature}

/-- The literal non-test observed feature profile `theta_j = q + epsilon_j`. -/
def lg21ContinuousPopulationBase
    {Feature : Type*} (testFeature : Feature) :
    Bool × (ℝ × (Feature → ℝ)) → LG21NonTestFeature Feature testFeature → ℝ :=
  fun student feature => lg21ContinuousPopulationFeature feature.1 student

/-- The non-test profile is measurable on the literal source population. -/
theorem lg21ContinuousPopulationBase_measurable
    {Feature : Type*} (testFeature : Feature) :
    Measurable (lg21ContinuousPopulationBase testFeature) := by
  apply measurable_pi_lambda
  intro feature
  change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) =>
    student.2.1 + student.2.2 feature.1
  exact (measurable_fst.comp measurable_snd).add
    ((measurable_pi_apply feature.1).comp (measurable_snd.comp measurable_snd))

/-- The positive-access normalized population is a probability law. -/
theorem lg21ContinuousGaussianAccessPopulationLaw_isProbability
    {Feature : Type*} [Fintype Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) :
    IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) := by
  letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
  letI : IsProbabilityMeasure (lg21ContinuousGaussianNoiseLaw M) := by
    unfold lg21ContinuousGaussianNoiseLaw
    infer_instance
  letI : IsProbabilityMeasure
      (lg21ContinuousGaussianStudentPrimitiveLaw M) := by
    unfold lg21ContinuousGaussianStudentPrimitiveLaw
    infer_instance
  letI : IsProbabilityMeasure (lg21ContinuousGaussianPopulationLaw M) := by
    exact lg21ContinuousGaussianPopulationLaw_isProbability M
  apply lg21NormalizedRestriction_isProbability
  · have hfactor := lg21ContinuousGaussianPopulation_access_student_factorization M
      ({true} : Set Bool) (Set.univ : Set (ℝ × (Feature → ℝ)))
    change lg21ContinuousGaussianPopulationLaw M
        {student | lg21ContinuousPopulationAccess student = true} ≠ 0
    rw [show {student : Bool × (ℝ × (Feature → ℝ)) |
        lg21ContinuousPopulationAccess student = true} =
        ({true} : Set Bool) ×ˢ Set.univ by
          ext student
          change student.1 = true ↔ student.1 = true ∧ student.2 ∈ Set.univ
          simp,
      hfactor]
    rw [IsProbabilityMeasure.measure_univ, mul_one]
    exact ne_of_gt haccess
  · exact measure_ne_top _ _

/--
The literal positive-access population has the canonical raw disintegration of
the `(score, skill)` pair over the actual non-test base profile.  This is an
exact measure identity; it does not yet identify the resulting conditional
kernel with a closed-form Gaussian posterior or with the school PBO.
-/
theorem lg21ContinuousGaussianAccessPopulation_raw_base_score_skill_disintegration
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature) :
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    letI : IsFiniteMeasure
        (lg21ContinuousGaussianAccessPopulationLaw M) :=
      ⟨by simp⟩
    (lg21ContinuousGaussianAccessPopulationLaw M).map
        (fun student =>
          (lg21ContinuousPopulationBase testFeature student,
            (lg21ContinuousPopulationFeature testFeature student,
              lg21ContinuousPopulationSkill student))) =
      (lg21ContinuousGaussianAccessPopulationLaw M).map
          (lg21ContinuousPopulationBase testFeature) ⊗ₘ
        condDistrib
          (fun student =>
            (lg21ContinuousPopulationFeature testFeature student,
              lg21ContinuousPopulationSkill student))
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousGaussianAccessPopulationLaw M) := by
  let law := lg21ContinuousGaussianAccessPopulationLaw M
  letI : IsProbabilityMeasure law := by
    exact lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure law := ⟨by simp⟩
  have hskill : Measurable (lg21ContinuousPopulationSkill (Feature := Feature)) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  have hnoise : Measurable
      (lg21ContinuousPopulationNoise (Feature := Feature) testFeature) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.2 testFeature
    exact (measurable_pi_apply testFeature).comp
      (measurable_snd.comp measurable_snd)
  have hscore : Measurable
      (lg21ContinuousPopulationFeature (Feature := Feature) testFeature) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) =>
      student.2.1 + student.2.2 testFeature
    exact hskill.add hnoise
  have hscoreSkill : Measurable
      (fun student : Bool × (ℝ × (Feature → ℝ)) =>
        (lg21ContinuousPopulationFeature testFeature student,
          lg21ContinuousPopulationSkill student)) :=
    hscore.prodMk hskill
  change law.map
      (fun student =>
        (lg21ContinuousPopulationBase testFeature student,
          (lg21ContinuousPopulationFeature testFeature student,
            lg21ContinuousPopulationSkill student))) =
      law.map (lg21ContinuousPopulationBase testFeature) ⊗ₘ
        condDistrib
          (fun student =>
            (lg21ContinuousPopulationFeature testFeature student,
              lg21ContinuousPopulationSkill student))
          (lg21ContinuousPopulationBase testFeature) law
  symm
  exact compProd_map_condDistrib hscoreSkill.aemeasurable

/--
The literal access-conditioned population also satisfies the nested
almost-everywhere conditional-law factorization for `(score, skill)` given
the actual non-test base profile.  This is a direct disintegration theorem;
it does not identify either conditional kernel with a closed-form Gaussian
posterior or with a school PBO.
-/
theorem lg21ContinuousGaussianAccessPopulation_base_score_skill_chain_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature) :
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    letI : IsFiniteMeasure
        (lg21ContinuousGaussianAccessPopulationLaw M) :=
      ⟨by simp⟩
    condDistrib
        (fun student =>
          (lg21ContinuousPopulationFeature testFeature student,
            lg21ContinuousPopulationSkill student))
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousGaussianAccessPopulationLaw M) =ᵐ[
          (lg21ContinuousGaussianAccessPopulationLaw M).map
            (lg21ContinuousPopulationBase testFeature)]
      condDistrib
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousGaussianAccessPopulationLaw M) ⊗ₖ
        condDistrib
          (lg21ContinuousPopulationSkill)
          (fun student =>
            (lg21ContinuousPopulationBase testFeature student,
              lg21ContinuousPopulationFeature testFeature student))
          (lg21ContinuousGaussianAccessPopulationLaw M) := by
  let law := lg21ContinuousGaussianAccessPopulationLaw M
  letI : IsProbabilityMeasure law := by
    exact lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure law := ⟨by simp⟩
  have hskill : Measurable (lg21ContinuousPopulationSkill (Feature := Feature)) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  have hnoise : Measurable
      (lg21ContinuousPopulationNoise (Feature := Feature) testFeature) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) =>
      student.2.2 testFeature
    exact (measurable_pi_apply testFeature).comp
      (measurable_snd.comp measurable_snd)
  have hscore : Measurable
      (lg21ContinuousPopulationFeature (Feature := Feature) testFeature) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) =>
      student.2.1 + student.2.2 testFeature
    exact hskill.add hnoise
  exact condDistrib_score_skill_chain_ae law
    (lg21ContinuousPopulationBase testFeature)
    (lg21ContinuousPopulationFeature testFeature)
    lg21ContinuousPopulationSkill
    (lg21ContinuousPopulationBase_measurable testFeature) hscore hskill

/--
Conditioning a positive-access product population on `Z = 1` leaves the
latent student block unchanged.  This is the literal source-law bridge behind
the informal statement that access is independent of skill and features.
-/
theorem lg21ContinuousGaussianAccessPopulation_map_student_eq
    {Feature : Type*} [Fintype Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) :
    (lg21ContinuousGaussianAccessPopulationLaw M).map Prod.snd =
      lg21ContinuousGaussianStudentPrimitiveLaw M := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let studentLaw := lg21ContinuousGaussianStudentPrimitiveLaw M
  let accessEvent : Set (Bool × (ℝ × (Feature → ℝ))) :=
    {student | lg21ContinuousPopulationAccess student = true}
  have hraw_probability : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsProbabilityMeasure rawLaw := hraw_probability
  letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
  have hstudent_probability : IsProbabilityMeasure studentLaw := by
    unfold studentLaw lg21ContinuousGaussianStudentPrimitiveLaw
    unfold lg21ContinuousGaussianNoiseLaw
    infer_instance
  letI : IsProbabilityMeasure studentLaw := hstudent_probability
  have haccessEvent : accessEvent = ({true} : Set Bool) ×ˢ Set.univ := by
    ext student
    change student.1 = true ↔ student.1 = true ∧ student.2 ∈ Set.univ
    simp
  have hraw_access : rawLaw accessEvent = M.accessLaw {true} := by
    rw [haccessEvent, lg21ContinuousGaussianPopulation_access_student_factorization]
    simp [studentLaw]
  have haccess_ne_zero : rawLaw accessEvent ≠ 0 := by
    rw [hraw_access]
    exact ne_of_gt haccess
  have haccess_ne_top : rawLaw accessEvent ≠ ⊤ := by
    rw [hraw_access]
    exact measure_ne_top _ _
  ext target htarget
  rw [Measure.map_apply (measurable_snd) htarget]
  change lg21NormalizedRestriction rawLaw accessEvent (Prod.snd ⁻¹' target) =
    studentLaw target
  rw [lg21NormalizedRestriction_apply rawLaw (measurable_snd htarget)]
  have hpreimage :
      Prod.snd ⁻¹' target ∩ accessEvent = ({true} : Set Bool) ×ˢ target := by
    rw [haccessEvent]
    ext student
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff,
      Set.mem_univ, and_true]
    constructor <;> intro h
    · exact ⟨h.2, h.1⟩
    · exact ⟨h.2, h.1⟩
  rw [hpreimage]
  rw [show rawLaw = lg21ContinuousGaussianPopulationLaw M by rfl,
    lg21ContinuousGaussianPopulation_access_student_factorization]
  rw [hraw_access]
  rw [← mul_assoc, ENNReal.inv_mul_cancel (ne_of_gt haccess) (measure_ne_top _ _), one_mul]

/-- The observed-access latent-skill marginal is the source Gaussian prior. -/
theorem lg21ContinuousGaussianAccessPopulation_skill_marginal
    {Feature : Type*} [Fintype Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) :
    (lg21ContinuousGaussianAccessPopulationLaw M).map
        lg21ContinuousPopulationSkill =
      gaussianReal M.priorMean M.priorVariance := by
  rw [show lg21ContinuousPopulationSkill =
      fun student => student.2.1 by rfl]
  rw [show (fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.1) =
      (fun primitive : ℝ × (Feature → ℝ) => primitive.1) ∘ Prod.snd by rfl,
    ← Measure.map_map]
  · rw [lg21ContinuousGaussianAccessPopulation_map_student_eq M haccess]
    ext event hevent
    rw [Measure.map_apply measurable_fst hevent]
    have hpreimage :
        (Prod.fst : ℝ × (Feature → ℝ) → ℝ) ⁻¹' event =
          event ×ˢ (Set.univ : Set (Feature → ℝ)) := by
      ext primitive
      change primitive.1 ∈ event ↔ primitive.1 ∈ event ∧ primitive.2 ∈ Set.univ
      simp
    rw [hpreimage]
    exact lg21ContinuousGaussianStudentPrimitiveLaw_skill_marginal M event
  · exact measurable_fst
  · exact measurable_snd

/-- A single coordinate of the independent source noise vector has its stated Gaussian law. -/
theorem lg21ContinuousGaussianNoiseLaw_map_eval_eq
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature) :
    (lg21ContinuousGaussianNoiseLaw M).map (Function.eval testFeature) =
      gaussianReal 0 (M.noiseVariance testFeature) := by
  unfold lg21ContinuousGaussianNoiseLaw
  rw [Measure.pi_map_eval]
  simp

/--
The literal student block has the product law of latent skill and a chosen
test-noise coordinate.  The product is retained rather than summarized by a
name, so later score and posterior arguments cannot silently assume
independence.
-/
theorem lg21ContinuousGaussianStudentPrimitiveLaw_skill_noise_joint
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature) :
    (lg21ContinuousGaussianStudentPrimitiveLaw M).map
        (fun primitive => (primitive.1, primitive.2 testFeature)) =
      (gaussianReal M.priorMean M.priorVariance).prod
        (gaussianReal 0 (M.noiseVariance testFeature)) := by
  let prior := gaussianReal M.priorMean M.priorVariance
  let noiseLaw := lg21ContinuousGaussianNoiseLaw M
  letI : IsProbabilityMeasure noiseLaw := by
    unfold noiseLaw lg21ContinuousGaussianNoiseLaw
    infer_instance
  change Measure.map
      (fun primitive : ℝ × (Feature → ℝ) => (primitive.1, primitive.2 testFeature))
      (prior.prod noiseLaw) =
    prior.prod (gaussianReal 0 (M.noiseVariance testFeature))
  calc
    Measure.map
        (fun primitive : ℝ × (Feature → ℝ) => (primitive.1, primitive.2 testFeature))
        (prior.prod noiseLaw) =
      Measure.map (Prod.map id (Function.eval testFeature))
        (prior.prod noiseLaw) := by rfl
    _ = (Measure.map id prior).prod
        (Measure.map (Function.eval testFeature) noiseLaw) :=
      (Measure.map_prod_map prior noiseLaw measurable_id
        (measurable_pi_apply testFeature)).symm
    _ = prior.prod (gaussianReal 0 (M.noiseVariance testFeature)) := by
      rw [lg21ContinuousGaussianNoiseLaw_map_eval_eq M testFeature]
      simp

/--
The observed-access population has the same literal `(skill, test-noise)`
product law after conditioning on positive access.
-/
theorem lg21ContinuousGaussianAccessPopulation_skill_noise_joint
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature) :
    (lg21ContinuousGaussianAccessPopulationLaw M).map
        (fun student =>
          (lg21ContinuousPopulationSkill student,
            lg21ContinuousPopulationNoise testFeature student)) =
      (gaussianReal M.priorMean M.priorVariance).prod
        (gaussianReal 0 (M.noiseVariance testFeature)) := by
  let pairOfPrimitive : ℝ × (Feature → ℝ) → ℝ × ℝ :=
    fun primitive => (primitive.1, primitive.2 testFeature)
  have hpair_measurable : Measurable pairOfPrimitive := by
    exact measurable_fst.prodMk
      ((measurable_pi_apply testFeature).comp measurable_snd)
  calc
    (lg21ContinuousGaussianAccessPopulationLaw M).map
        (fun student =>
          (lg21ContinuousPopulationSkill student,
            lg21ContinuousPopulationNoise testFeature student)) =
      (lg21ContinuousGaussianAccessPopulationLaw M).map
        (pairOfPrimitive ∘ Prod.snd) := by rfl
    _ = ((lg21ContinuousGaussianAccessPopulationLaw M).map Prod.snd).map
        pairOfPrimitive :=
      (Measure.map_map hpair_measurable measurable_snd).symm
    _ = (lg21ContinuousGaussianStudentPrimitiveLaw M).map pairOfPrimitive := by
      rw [lg21ContinuousGaussianAccessPopulation_map_student_eq M haccess]
    _ = (gaussianReal M.priorMean M.priorVariance).prod
        (gaussianReal 0 (M.noiseVariance testFeature)) := by
      exact lg21ContinuousGaussianStudentPrimitiveLaw_skill_noise_joint M testFeature

/-- The literal observed-access `(skill, score)` law is the image of the displayed product law. -/
theorem lg21ContinuousGaussianAccessPopulation_skill_score_joint
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature) :
    (lg21ContinuousGaussianAccessPopulationLaw M).map
        (fun student =>
          (lg21ContinuousPopulationSkill student,
            lg21ContinuousPopulationFeature testFeature student)) =
      ((gaussianReal M.priorMean M.priorVariance).prod
        (gaussianReal 0 (M.noiseVariance testFeature))).map
          (fun pair => (pair.1, pair.1 + pair.2)) := by
  let skillNoise : (Bool × (ℝ × (Feature → ℝ))) → ℝ × ℝ :=
    fun student =>
      (lg21ContinuousPopulationSkill student,
        lg21ContinuousPopulationNoise testFeature student)
  let skillScore : ℝ × ℝ → ℝ × ℝ :=
    fun pair => (pair.1, pair.1 + pair.2)
  have hskillNoise_measurable : Measurable skillNoise := by
    have hskill : Measurable (lg21ContinuousPopulationSkill (Feature := Feature)) := by
      change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.1
      exact measurable_fst.comp measurable_snd
    have hnoise : Measurable
        (lg21ContinuousPopulationNoise (Feature := Feature) testFeature) := by
      change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.2 testFeature
      exact (measurable_pi_apply testFeature).comp
        (measurable_snd.comp measurable_snd)
    exact hskill.prodMk hnoise
  have hskillScore_measurable : Measurable skillScore := by
    exact measurable_fst.prodMk (measurable_fst.add measurable_snd)
  calc
    (lg21ContinuousGaussianAccessPopulationLaw M).map
        (fun student =>
          (lg21ContinuousPopulationSkill student,
            lg21ContinuousPopulationFeature testFeature student)) =
      (lg21ContinuousGaussianAccessPopulationLaw M).map
        (skillScore ∘ skillNoise) := by rfl
    _ = ((lg21ContinuousGaussianAccessPopulationLaw M).map skillNoise).map
        skillScore :=
      (Measure.map_map hskillScore_measurable
        hskillNoise_measurable).symm
    _ = ((gaussianReal M.priorMean M.priorVariance).prod
        (gaussianReal 0 (M.noiseVariance testFeature))).map skillScore := by
      rw [show skillNoise = fun student =>
        (lg21ContinuousPopulationSkill student,
          lg21ContinuousPopulationNoise testFeature student) by rfl,
        lg21ContinuousGaussianAccessPopulation_skill_noise_joint M haccess testFeature]

end

end LG21TestOptionalPolicies
