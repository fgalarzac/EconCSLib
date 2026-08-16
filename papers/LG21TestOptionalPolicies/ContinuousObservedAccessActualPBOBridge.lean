import LG21TestOptionalPolicies.ContinuousObservedAccessSourceConditionalKernel

/-!
# Actual conditional-expectation bridge for the LG21 observed-access population

This module establishes the narrow source-literal bridge that is available
before strategic actions are introduced.  On the population conditional on
`Z = 1`, the mean of the factory's literal regular conditional distribution of
latent skill given the non-test base profile and an observed score is an
almost-everywhere version of the corresponding conditional expectation.

This is deliberately an *unselected* `(base, score)` statement.  It is not an
identification of the paper's full PBO after an action history.  In particular,
optional reporting requires conditioning on the observed report action, and
report-required testing selects on latent skill before the score is observed.
Neither action-selected posterior is derived here.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory
open ProbabilityTheory

/--
The literal latent-skill coordinate is integrable under the positive-access
source population.  This follows from its proved Gaussian marginal, rather
than from a posterior or PBO assumption.
-/
theorem lg21ContinuousGaussianAccessPopulation_skill_integrable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) :
    Integrable (lg21ContinuousPopulationSkill (Feature := Feature))
      (lg21ContinuousGaussianAccessPopulationLaw M) := by
  have hgaussian : Integrable (fun skill : ℝ => skill)
      (gaussianReal M.priorMean M.priorVariance) := by
    apply integrable_of_mem_interior_integrableExpSet
    simp
  rw [← lg21ContinuousGaussianAccessPopulation_skill_marginal M haccess] at hgaussian
  exact (integrable_map_measure stronglyMeasurable_id.aestronglyMeasurable
    (by
      exact (measurable_fst.comp measurable_snd).aemeasurable)).mp
    (by simpa [Function.comp_def] using hgaussian)

/--
The unselected observed-access PBO candidate: the conditional latent-skill
mean after the school has observed `Z = 1`, the non-test base profile, and the
raw test score.  Its name records the source interpretation, but it omits the
report action deliberately; it must not be substituted for an action-selected
PBO without a separate observation-map proof.
-/
def lg21ContinuousObservedAccessUnselectedPBO
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (base : LG21NonTestFeature Feature testFeature → ℝ) (score : ℝ) : ℝ :=
  let source :=
    lg21ContinuousObservedAccessSourceConditionalKernel M haccess testFeature
  source.posteriorSkillMean base score

/--
On the literal `Z = 1` population, the unselected PBO candidate is the
conditional expectation of latent skill given `(base, score)`.  The equality
is only almost everywhere in the positive-access population: neither regular
conditional distributions nor conditional expectations determine values on
null observation fibres.

This is not a source credit for Lemma 4.1.  It conditions on a raw score that
is already observed, not on the paper's full `(Z, base, X, X * score)` action
history.  Hence it does not establish a no-report PBO, an off-path reporter
PBO, or the selection-aware reporter PBO required after a skill-dependent
taking decision.
-/
theorem lg21ContinuousObservedAccess_unselectedPBO_eq_condExp_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature) :
    let source :=
      lg21ContinuousObservedAccessSourceConditionalKernel M haccess testFeature
    source.populationLaw[
      source.skill |
        MeasurableSpace.comap
          (fun student => (source.base student, source.score student)) inferInstance] =ᵐ[
        source.populationLaw]
      fun student =>
        lg21ContinuousObservedAccessUnselectedPBO M haccess testFeature
          (source.base student) (source.score student) := by
  intro source
  have hintegrable : Integrable source.skill source.populationLaw := by
    change Integrable (lg21ContinuousPopulationSkill (Feature := Feature))
      (lg21ContinuousGaussianAccessPopulationLaw M)
    exact lg21ContinuousGaussianAccessPopulation_skill_integrable M haccess
  change source.populationLaw[
      source.skill |
        MeasurableSpace.comap
          (fun student => (source.base student, source.score student)) inferInstance] =ᵐ[
        source.populationLaw]
      fun student =>
        ∫ skill, skill ∂condDistrib source.skill
          (fun other => (source.base other, source.score other))
          source.populationLaw
          (source.base student, source.score student)
  exact condExp_ae_eq_integral_condDistrib'
    (source.base_measurable.prodMk source.score_measurable) hintegrable

end

end LG21TestOptionalPolicies
