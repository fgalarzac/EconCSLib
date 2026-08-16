import LG21TestOptionalPolicies.ContinuousAccessConditionedPopulation
import LG21TestOptionalPolicies.ObservedAccessSourceConditionalKernel

/-!
# Literal conditional-kernel instance for the LG21 access-conditioned population

This module instantiates the raw conditional-law interface directly from the
finite-dimensional source population.  Every kernel is the actual
`condDistrib` of the positive-access population; its two ordered
factorizations are derived from disintegration, rather than supplied as
assumptions.

The result is intentionally only a raw-probability bridge.  In particular it
does not identify a regular conditional distribution with a closed-form
Gaussian posterior on every fibre, and it does not identify any conditional
mean with a school PBO or an action-contingent payoff.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory
open ProbabilityTheory
open Set

/--
The source's literal positive-access population supplies all raw
conditional-law evidence required by
`LG21ObservedAccessSourceConditionalKernel`.  The kernels are not opaque
parameters: they are the regular conditional distributions of the actual
access-conditioned source law.

The conclusion is a measure-theoretic instance only.  Its `condDistrib`
kernels are specified only almost everywhere in the corresponding observation
marginal, as required by the source-faithful interface.
-/
def lg21ContinuousObservedAccessSourceConditionalKernel
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature) :
    LG21ObservedAccessSourceConditionalKernel
      (Bool × (ℝ × (Feature → ℝ)))
      (LG21NonTestFeature Feature testFeature → ℝ) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let law := lg21ContinuousGaussianAccessPopulationLaw M
  let base := lg21ContinuousPopulationBase testFeature
  let skill := lg21ContinuousPopulationSkill (Feature := Feature)
  let score := lg21ContinuousPopulationFeature testFeature
  letI : IsProbabilityMeasure rawLaw := by
    exact lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsProbabilityMeasure law := by
    exact lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure law := ⟨by simp⟩
  have hbase : Measurable base := by
    exact lg21ContinuousPopulationBase_measurable testFeature
  have hskill : Measurable skill := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  have hscore : Measurable score := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) =>
      student.2.1 + student.2.2 testFeature
    exact hskill.add
      ((measurable_pi_apply testFeature).comp
        (measurable_snd.comp measurable_snd))
  have hraw_access :
      rawLaw {student | lg21ContinuousPopulationAccess student = true} =
        M.accessLaw {true} := by
    rw [show {student : Bool × (ℝ × (Feature → ℝ)) |
        lg21ContinuousPopulationAccess student = true} =
        ({true} : Set Bool) ×ˢ Set.univ by
          ext student
          change student.1 = true ↔ student.1 = true ∧ student.2 ∈ Set.univ
          simp,
      show rawLaw = lg21ContinuousGaussianPopulationLaw M by rfl,
      lg21ContinuousGaussianPopulation_access_student_factorization]
    simp [lg21ContinuousGaussianStudentPrimitiveLaw,
      lg21ContinuousGaussianNoiseLaw]
  refine
    { rawPopulationLaw := rawLaw
      rawPopulationLaw_isProbability := inferInstance
      access := lg21ContinuousPopulationAccess
      access_measurable := measurable_fst
      access_positive := by
        rw [hraw_access]
        exact haccess
      populationLaw := law
      populationLaw_eq_access_conditioned := rfl
      populationLaw_isProbability := inferInstance
      base := base
      skill := skill
      score := score
      base_measurable := hbase
      skill_measurable := hskill
      score_measurable := hscore
      scoreSkillGivenBase := condDistrib (fun student => (score student, skill student)) base law
      scoreSkillGivenBase_isMarkov := inferInstance
      scoreGivenBase := condDistrib score base law
      scoreGivenBase_isMarkov := inferInstance
      skillGivenBaseScore :=
        condDistrib skill (fun student => (base student, score student)) law
      skillGivenBaseScore_isMarkov := inferInstance
      raw_score_skill_disintegration := by
        change law.map (fun student =>
          (base student, (score student, skill student))) =
          law.map base ⊗ₘ condDistrib (fun student => (score student, skill student)) base law
        symm
        exact compProd_map_condDistrib (hscore.prodMk hskill).aemeasurable
      score_skill_kernel_factorization := by
        exact condDistrib_score_skill_chain_ae law base score skill hbase hscore hskill
      skillScoreGivenBase := condDistrib (fun student => (skill student, score student)) base law
      skillScoreGivenBase_isMarkov := inferInstance
      skillGivenBase := condDistrib skill base law
      skillGivenBase_isMarkov := inferInstance
      scoreGivenBaseSkill :=
        condDistrib score (fun student => (base student, skill student)) law
      scoreGivenBaseSkill_isMarkov := inferInstance
      raw_skill_score_disintegration := by
        change law.map (fun student =>
          (base student, (skill student, score student))) =
          law.map base ⊗ₘ condDistrib (fun student => (skill student, score student)) base law
        symm
        exact compProd_map_condDistrib (hskill.prodMk hscore).aemeasurable
      skill_score_kernel_factorization := by
        exact condDistrib_score_skill_chain_ae law base skill score hbase hskill hscore }

/--
The optional-order factorization of the literal population, stated directly
for the concrete instance.  This is retained as an easy-to-inspect endpoint
for downstream source bridges; it makes no Gaussian or PBO assertion.
-/
theorem lg21ContinuousObservedAccess_condDistrib_score_skill_chain_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature) :
    let source :=
      lg21ContinuousObservedAccessSourceConditionalKernel M haccess testFeature
    condDistrib (fun student => (source.score student, source.skill student))
      source.base source.populationLaw =ᵐ[source.populationLaw.map source.base]
      source.scoreGivenBase ⊗ₖ source.skillGivenBaseScore := by
  intro source
  exact source.condDistrib_score_skill_eq_score_then_posterior_ae

/--
The report-required-order factorization of the literal population, stated
directly for the concrete instance.  It likewise stops before any PBO or
Gaussian-posterior identification.
-/
theorem lg21ContinuousObservedAccess_condDistrib_skill_score_chain_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature) :
    let source :=
      lg21ContinuousObservedAccessSourceConditionalKernel M haccess testFeature
    condDistrib (fun student => (source.skill student, source.score student))
      source.base source.populationLaw =ᵐ[source.populationLaw.map source.base]
      source.skillGivenBase ⊗ₖ source.scoreGivenBaseSkill := by
  intro source
  exact source.condDistrib_skill_score_eq_skill_then_score_ae

end

end LG21TestOptionalPolicies
