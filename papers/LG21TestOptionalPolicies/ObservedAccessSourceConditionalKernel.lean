import LG21TestOptionalPolicies.ContinuousPopulation
import LG21TestOptionalPolicies.ObservedAccessContinuous
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Disintegration.Integral

/-!
# Source-conditional kernel interface for LG21 observed access

This module records the measure-theoretic bridge that a source-faithful
observed-access proof must establish before it can use any fixed-base PBO
calculation.  In particular, it does not condition on a singleton continuous
base profile.

The fields below are exact identities of the raw joint population law with
kernel compositions.  They are deliberately *evidence obligations*, not
conclusions inferred from names such as `scoreLaw` or `posterior`.  The
current `LG21ContinuousGaussianPopulation` supplies the raw product law but
does not yet prove these identities.  Consequently, this file has no
paper-credit endpoint and contains no equilibrium, cutoff, Gaussian-posterior,
or PBO-consistency assumption.

Once an instantiation proves the displayed raw identities, the theorems here
provide three reusable facts:

* the named kernels are genuine regular conditional distributions, globally
  almost everywhere in the base marginal;
* the score/skill conditional joint law has the stated posterior
  factorization almost everywhere in base profiles;
* conditioning that joint law on a positive-mass action event transports its
  skill mean to the integral of posterior skill means over the restricted
  score law.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory
open ProbabilityTheory

open scoped ProbabilityTheory

/-! ## Raw conditional-law evidence -/

/--
The source conditional-law evidence needed for the observed-access part of
LG21.  The two orderings are both retained because optional reporting uses
`score | base` followed by `skill | base, score`, while report-required taking
uses `skill | base` followed by `score | base, skill`.

Every conditional-law assertion is an equality of the raw joint measure with
a measure/kernel composition.  This is the form that must be derived from the
literal finite Gaussian product population; a bare parameter equality or a
field named `PBO` would not establish it.
-/
structure LG21ObservedAccessSourceConditionalKernel
    (Ω Base : Type*) [MeasurableSpace Ω] [MeasurableSpace Base] where
  /-- The literal, unrestricted source population measure. -/
  rawPopulationLaw : Measure Ω
  rawPopulationLaw_isProbability : IsProbabilityMeasure rawPopulationLaw
  /-- Source access indicator `Z`. -/
  access : Ω → Bool
  access_measurable : Measurable access
  /-- The observed-access branch is a genuine positive-probability carrier. -/
  access_positive :
    0 < rawPopulationLaw {ω | access ω = true}
  /--
  The one population measure on which the conditional kernels below are
  formed.  It is deliberately separate from the raw source population: every
  Lemma 4.1 PBO calculation is conditional on observed access `Z = 1`.
  -/
  populationLaw : Measure Ω
  /--
  The conditional-kernel carrier is exactly the normalized `Z = 1` source
  population.  This prevents a hidden-access population from being relabelled
  as an observed-access model.
  -/
  populationLaw_eq_access_conditioned :
    populationLaw = lg21NormalizedRestriction rawPopulationLaw
      {ω | access ω = true}
  populationLaw_isProbability : IsProbabilityMeasure populationLaw
  /-- The observed non-test profile. -/
  base : Ω → Base
  /-- Latent skill. -/
  skill : Ω → ℝ
  /-- The observed test score. -/
  score : Ω → ℝ
  base_measurable : Measurable base
  skill_measurable : Measurable skill
  score_measurable : Measurable score

  /-- Conditional joint law in optional-reporting order `(score, skill)`. -/
  scoreSkillGivenBase : Kernel Base (ℝ × ℝ)
  scoreSkillGivenBase_isMarkov : IsMarkovKernel scoreSkillGivenBase
  /-- Candidate score kernel indexed by the base profile. -/
  scoreGivenBase : Kernel Base ℝ
  scoreGivenBase_isMarkov : IsMarkovKernel scoreGivenBase
  /-- Candidate posterior skill kernel indexed by `(base, score)`. -/
  skillGivenBaseScore : Kernel (Base × ℝ) ℝ
  skillGivenBaseScore_isMarkov : IsMarkovKernel skillGivenBaseScore

  /--
  First source-derived obligation: the literal raw population disintegrates
  into the optional-reporting-order joint conditional law.
  -/
  raw_score_skill_disintegration :
    populationLaw.map (fun ω => (base ω, (score ω, skill ω))) =
      populationLaw.map base ⊗ₘ scoreSkillGivenBase
  /--
  Second source-derived obligation: that same conditional joint law factors
  through the score law and posterior skill kernel, almost everywhere in the
  actual base marginal.
  -/
  score_skill_kernel_factorization :
    scoreSkillGivenBase =ᵐ[populationLaw.map base]
      scoreGivenBase ⊗ₖ skillGivenBaseScore

  /-- Conditional joint law in report-required order `(skill, score)`. -/
  skillScoreGivenBase : Kernel Base (ℝ × ℝ)
  skillScoreGivenBase_isMarkov : IsMarkovKernel skillScoreGivenBase
  /-- Candidate conditional skill law indexed by the base profile. -/
  skillGivenBase : Kernel Base ℝ
  skillGivenBase_isMarkov : IsMarkovKernel skillGivenBase
  /-- Candidate conditional test law indexed by `(base, skill)`. -/
  scoreGivenBaseSkill : Kernel (Base × ℝ) ℝ
  scoreGivenBaseSkill_isMarkov : IsMarkovKernel scoreGivenBaseSkill

  /--
  Third source-derived obligation: the raw population disintegrates in the
  report-required order.
  -/
  raw_skill_score_disintegration :
    populationLaw.map (fun ω => (base ω, (skill ω, score ω))) =
      populationLaw.map base ⊗ₘ skillScoreGivenBase
  /--
  Fourth source-derived obligation: the report-required joint kernel factors
  by first drawing conditional skill and then test noise.
  -/
  skill_score_kernel_factorization :
    skillScoreGivenBase =ᵐ[populationLaw.map base]
      skillGivenBase ⊗ₖ scoreGivenBaseSkill

namespace LG21ObservedAccessSourceConditionalKernel

variable {Ω Base : Type*} [MeasurableSpace Ω] [MeasurableSpace Base]

/-! The evidence fields are registered only as local implementation instances. -/

instance populationLaw_isProbability_instance
    (M : LG21ObservedAccessSourceConditionalKernel Ω Base) :
    IsProbabilityMeasure M.populationLaw :=
  M.populationLaw_isProbability

instance scoreSkillGivenBase_isMarkov_instance
    (M : LG21ObservedAccessSourceConditionalKernel Ω Base) :
    IsMarkovKernel M.scoreSkillGivenBase :=
  M.scoreSkillGivenBase_isMarkov

instance scoreGivenBase_isMarkov_instance
    (M : LG21ObservedAccessSourceConditionalKernel Ω Base) :
    IsMarkovKernel M.scoreGivenBase :=
  M.scoreGivenBase_isMarkov

instance skillGivenBaseScore_isMarkov_instance
    (M : LG21ObservedAccessSourceConditionalKernel Ω Base) :
    IsMarkovKernel M.skillGivenBaseScore :=
  M.skillGivenBaseScore_isMarkov

instance skillScoreGivenBase_isMarkov_instance
    (M : LG21ObservedAccessSourceConditionalKernel Ω Base) :
    IsMarkovKernel M.skillScoreGivenBase :=
  M.skillScoreGivenBase_isMarkov

instance skillGivenBase_isMarkov_instance
    (M : LG21ObservedAccessSourceConditionalKernel Ω Base) :
    IsMarkovKernel M.skillGivenBase :=
  M.skillGivenBase_isMarkov

instance scoreGivenBaseSkill_isMarkov_instance
    (M : LG21ObservedAccessSourceConditionalKernel Ω Base) :
    IsMarkovKernel M.scoreGivenBaseSkill :=
  M.scoreGivenBaseSkill_isMarkov

/-! ## Regular-conditional-distribution consequences -/

/-- The optional-order joint kernel is a genuine RCD of `(score, skill)` given base. -/
theorem condDistrib_score_skill_ae
    (M : LG21ObservedAccessSourceConditionalKernel Ω Base) :
    condDistrib (fun ω => (M.score ω, M.skill ω)) M.base M.populationLaw =ᵐ[
        M.populationLaw.map M.base] M.scoreSkillGivenBase := by
  exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    M.base_measurable (M.score_measurable.prodMk M.skill_measurable)
    M.raw_score_skill_disintegration

/-- The report-required-order joint kernel is a genuine RCD of `(skill, score)` given base. -/
theorem condDistrib_skill_score_ae
    (M : LG21ObservedAccessSourceConditionalKernel Ω Base) :
    condDistrib (fun ω => (M.skill ω, M.score ω)) M.base M.populationLaw =ᵐ[
        M.populationLaw.map M.base] M.skillScoreGivenBase := by
  exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    M.base_measurable (M.skill_measurable.prodMk M.score_measurable)
    M.raw_skill_score_disintegration

/--
The optional-order RCD factors through score and posterior skill kernels on
the actual base marginal.  This is the globally-a.e. replacement for an
invalid singleton-base conditioning step.
-/
theorem condDistrib_score_skill_eq_score_then_posterior_ae
    (M : LG21ObservedAccessSourceConditionalKernel Ω Base) :
    condDistrib (fun ω => (M.score ω, M.skill ω)) M.base M.populationLaw =ᵐ[
        M.populationLaw.map M.base]
      M.scoreGivenBase ⊗ₖ M.skillGivenBaseScore :=
  (M.condDistrib_score_skill_ae).trans M.score_skill_kernel_factorization

/-- The report-required RCD factors by conditional skill and then test noise. -/
theorem condDistrib_skill_score_eq_skill_then_score_ae
    (M : LG21ObservedAccessSourceConditionalKernel Ω Base) :
    condDistrib (fun ω => (M.skill ω, M.score ω)) M.base M.populationLaw =ᵐ[
        M.populationLaw.map M.base]
      M.skillGivenBase ⊗ₖ M.scoreGivenBaseSkill :=
  (M.condDistrib_skill_score_ae).trans M.skill_score_kernel_factorization

/--
The full-measure set of base profiles at which both conditional-law
identifications are valid pointwise.  The source disintegrations are only
almost-everywhere statements, so paper-facing fixed-fibre arguments must
quantify over this predicate (or remain explicitly almost everywhere).
-/
def sourceGoodBase
    (M : LG21ObservedAccessSourceConditionalKernel Ω Base) (base : Base) : Prop :=
  condDistrib (fun ω => (M.score ω, M.skill ω)) M.base M.populationLaw base =
      M.scoreSkillGivenBase base ∧
    M.scoreSkillGivenBase base =
      (M.scoreGivenBase ⊗ₖ M.skillGivenBaseScore) base ∧
    condDistrib (fun ω => (M.skill ω, M.score ω)) M.base M.populationLaw base =
      M.skillScoreGivenBase base ∧
    M.skillScoreGivenBase base =
      (M.skillGivenBase ⊗ₖ M.scoreGivenBaseSkill) base

/-- The source-good base profiles have full conditional-base measure. -/
theorem ae_sourceGoodBase
    (M : LG21ObservedAccessSourceConditionalKernel Ω Base) :
    ∀ᵐ base ∂M.populationLaw.map M.base, M.sourceGoodBase base := by
  filter_upwards [M.condDistrib_score_skill_ae,
    M.score_skill_kernel_factorization,
    M.condDistrib_skill_score_ae,
    M.skill_score_kernel_factorization] with base hOptional hOptionalFactor
      hRequired hRequiredFactor
  exact ⟨hOptional, hOptionalFactor, hRequired, hRequiredFactor⟩

/-! ## Action-event and tower transport -/

/-- Fixing a base profile turns the posterior kernel into a score-indexed kernel. -/
def posteriorSkillKernelAtBase
    (M : LG21ObservedAccessSourceConditionalKernel Ω Base) (base : Base) : Kernel ℝ ℝ :=
  M.skillGivenBaseScore.comap (fun score => (base, score))
    (measurable_const.prodMk measurable_id)

/--
The score law after a score-only selection event.  This is a construction on
the score/posterior experiment, not automatically the paper's full `X = 0`
cohort: in the optional protocol that cohort also includes `Y = 0` students
unless a separately proved all-taking carrier is supplied.
-/
def noReportScoreLaw
    (M : LG21ObservedAccessSourceConditionalKernel Ω Base)
    (reportDecision : Base → ℝ → Bool) (base : Base) : Measure ℝ :=
  lg21NormalizedRestriction (M.scoreGivenBase base)
    {score | reportDecision base score = false}

/--
The joint `(score, skill)` law in a score-selected cohort, built from the
score/posterior conditional experiment.  This is only a kernel construction;
its identification with the source's `X = 0` Bayesian estimate additionally
requires an all-taking carrier in the optional protocol, measurable action
events, the raw obligations above, and the Definition-1 PBO interpretation.
-/
def noReportScoreSkillLaw
    (M : LG21ObservedAccessSourceConditionalKernel Ω Base)
    (reportDecision : Base → ℝ → Bool) (base : Base) : Measure (ℝ × ℝ) := by
  exact (M.noReportScoreLaw reportDecision base) ⊗ₘ M.posteriorSkillKernelAtBase base

/-- The latent-skill marginal of the constructed no-report cohort. -/
def noReportSkillLaw
    (M : LG21ObservedAccessSourceConditionalKernel Ω Base)
    (reportDecision : Base → ℝ → Bool) (base : Base) : Measure ℝ :=
  (M.noReportScoreSkillLaw reportDecision base).map Prod.snd

/-- The posterior skill mean at a realized `(base, score)` pair. -/
def posteriorSkillMean
    (M : LG21ObservedAccessSourceConditionalKernel Ω Base)
    (base : Base) (score : ℝ) : ℝ :=
  ∫ skill, skill ∂M.skillGivenBaseScore (base, score)

/--
The score-selection tower identity.  It is purely measure-theoretic: after
restricting the conditional score law, the mean of the joint skill law equals
the restricted-score integral of posterior skill means.

No cutoff, PBO equality, Gaussian formula, all-taking fact, or action-event
measurability is assumed here.  A future paper-facing bridge may identify the
left hand side with the source PBO only after deriving the raw
conditional-kernel obligations from the population and proving those
additional sequential-action conditions.
-/
theorem noReportSkillMean_eq_posterior_tower
    (M : LG21ObservedAccessSourceConditionalKernel Ω Base)
    (reportDecision : Base → ℝ → Bool) (base : Base)
    (hintegrable :
      Integrable (fun pair : ℝ × ℝ => pair.2)
        (M.noReportScoreSkillLaw reportDecision base)) :
    (∫ skill, skill ∂M.noReportSkillLaw reportDecision base) =
      ∫ score, M.posteriorSkillMean base score ∂
        M.noReportScoreLaw reportDecision base := by
  letI : IsMarkovKernel M.skillGivenBaseScore := M.skillGivenBaseScore_isMarkov
  letI : IsMarkovKernel (M.posteriorSkillKernelAtBase base) := by
    unfold posteriorSkillKernelAtBase
    infer_instance
  letI : SFinite (M.noReportScoreLaw reportDecision base) := by
    unfold noReportScoreLaw lg21NormalizedRestriction
    infer_instance
  have hcomp := Measure.integral_compProd (μ := M.noReportScoreLaw reportDecision base)
    (κ := M.posteriorSkillKernelAtBase base) hintegrable
  calc
    (∫ skill, skill ∂M.noReportSkillLaw reportDecision base) =
        ∫ pair, pair.2 ∂M.noReportScoreSkillLaw reportDecision base := by
          unfold noReportSkillLaw
          exact integral_map_of_stronglyMeasurable measurable_snd stronglyMeasurable_id
    _ = ∫ score, M.posteriorSkillMean base score ∂
        M.noReportScoreLaw reportDecision base := by
          simpa [noReportScoreSkillLaw, posteriorSkillMean,
            posteriorSkillKernelAtBase, Kernel.comap_apply] using hcomp

/--
The report-required analogue selects the literal no-take action event from the
conditional skill law.  It is intentionally separate from any payoff or PBO
claim.
-/
def noTakeSkillLaw
    (M : LG21ObservedAccessSourceConditionalKernel Ω Base)
    (takeDecision : Base → ℝ → Bool) (base : Base) : Measure ℝ :=
  lg21NormalizedRestriction (M.skillGivenBase base)
    {skill | takeDecision base skill = false}

/-- A positive action branch makes the normalized no-report score law a probability measure. -/
theorem noReportScoreLaw_isProbability
    (M : LG21ObservedAccessSourceConditionalKernel Ω Base)
    (reportDecision : Base → ℝ → Bool) (base : Base)
    (hpositive : 0 < M.scoreGivenBase base {score | reportDecision base score = false}) :
    IsProbabilityMeasure (M.noReportScoreLaw reportDecision base) := by
  letI : IsFiniteMeasure (M.scoreGivenBase base) := inferInstance
  apply lg21NormalizedRestriction_isProbability
  · exact ne_of_gt hpositive
  · exact measure_ne_top _ _

/-- A positive action branch makes the normalized no-take skill law a probability measure. -/
theorem noTakeSkillLaw_isProbability
    (M : LG21ObservedAccessSourceConditionalKernel Ω Base)
    (takeDecision : Base → ℝ → Bool) (base : Base)
    (hpositive : 0 < M.skillGivenBase base {skill | takeDecision base skill = false}) :
    IsProbabilityMeasure (M.noTakeSkillLaw takeDecision base) := by
  letI : IsFiniteMeasure (M.skillGivenBase base) := inferInstance
  apply lg21NormalizedRestriction_isProbability
  · exact ne_of_gt hpositive
  · exact measure_ne_top _ _

end LG21ObservedAccessSourceConditionalKernel

end

end LG21TestOptionalPolicies
