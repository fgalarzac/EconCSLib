import LG21TestOptionalPolicies.ObservedAccessVoluntaryActiveBranchSelection
import LG21TestOptionalPolicies.ObservedAccessLemma41LiteralSourceCloseout

/-!
# Explicit source records for LG21's voluntary active-branch convention

These records expose the actual mathematical inputs of the Section 4 route.
They separate the common continuous Gaussian population from the two voluntary
protocols, so a result about one protocol does not silently require the other.
The active-branch field is a declared governing convention: it is not claimed
to be a consequence of the static RCD in Definition 1.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory

/-- The common literal Gaussian source population for observed-access Section
4 results. Positivity and nondegenerate-noise conditions are stated here rather
than inferred from the theorem name or from a selected profile. -/
structure LG21ObservedAccessGaussianSource
    (Feature : Type*) [Fintype Feature] [DecidableEq Feature] where
  population : LG21ContinuousGaussianPopulation Feature
  access_positive : 0 < population.accessLaw {true}
  test_feature : Feature
  prior_variance_positive : 0 < (population.priorVariance : ℝ)
  non_test_noise_variance_positive :
    ∀ feature : LG21NonTestFeature Feature test_feature,
      0 < (population.noiseVariance feature.1 : ℝ)
  test_noise_variance_positive :
    0 < (population.noiseVariance test_feature : ℝ)

/-- The selected optional-reporting profile and the declared active-branch
selection used to resolve the zero-probability action boundary. The selection
also requires a source-timed self-enforcing positive-mass representation of
the selected record; PBO, response, and closure obligations never assign a
value to an unattained branch. -/
structure LG21OptionalActiveBranchProfile
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature) where
  selected : LG21ObservedAccessOptionalPositiveMassRefinedEquilibrium
    source.population source.access_positive source.test_feature
  active_branch_selection : LG21OptionalFibrewiseActiveBranchSelection
    source.population source.access_positive source.test_feature selected

/-- The selected report-required-after-taking profile, its literal positive
branch PBO record, and the declared active-branch selection. The latter has a
source-timed self-enforcing representation of this record. No field assigns a
value to the null no-take branch. -/
structure LG21ReportRequiredActiveBranchProfile
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature) where
  selected : LG21ReportRequiredSequentialEquilibriumData ℝ
    (LG21NonTestFeature Feature source.test_feature -> ℝ) ℝ
  positive_branch_pbo :
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianAccessPopulationLaw source.population) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability source.population
        source.access_positive
    LG21ReportRequiredPositiveMassRefinedSourceEquilibrium
      (lg21ContinuousGaussianAccessPopulationLaw source.population)
      (lg21ContinuousPopulationBase source.test_feature)
      (lg21ContinuousPopulationFeature source.test_feature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) selected
      (source.population.noiseVariance source.test_feature)
  active_branch_selection : LG21ReportRequiredFibrewiseActiveBranchSelection
    source.population source.access_positive source.test_feature selected
    positive_branch_pbo

/-- The literal Gaussian source has a nonempty optional active-branch profile
under the declared Section 4 convention.  The selected source-timed candidate
is the all-take/all-report witness; maximality is immediate because that
candidate already activates the full feasible branch everywhere.  This is an
existence result for the declared convention, not a derivation from static RCD
semantics. -/
theorem lg21ObservedAccessGaussianSource_optionalActiveBranchProfile_nonempty
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature) :
    Nonempty (LG21OptionalActiveBranchProfile source) := by
  rcases
      lg21ContinuousGaussianAccessPopulation_exists_optionalSelfEnforcing_allTakeAllReport
        source.population source.access_positive source.test_feature
        source.prior_variance_positive source.non_test_noise_variance_positive
        source.test_noise_variance_positive with
    ⟨candidate, htake, hreport⟩
  let selected := candidate.source_timed
  let hselection : LG21OptionalFibrewiseActiveBranchSelection
      source.population source.access_positive source.test_feature selected :=
    { selected_self_enforcing := ⟨candidate, rfl⟩
      maximal_active_branch_ae := by
        dsimp [selected]
        intro other region hregion hpositive hcontains
        exact Filter.Eventually.of_forall fun student _ =>
          ⟨htake (lg21ContinuousPopulationSkill student)
              (lg21ContinuousPopulationBase source.test_feature student),
            hreport (lg21ContinuousPopulationBase source.test_feature student)
              (lg21ContinuousPopulationFeature source.test_feature student)⟩ }
  exact ⟨{ selected := selected, active_branch_selection := hselection }⟩

/-- The literal Gaussian source also has a nonempty report-required
active-branch profile under the declared Section 4 convention.  The chosen
candidate takes everywhere, so it witnesses maximality of the selected taking
branch without assigning a no-take PBO.  As above, this is existence for the
declared convention rather than a derivation from bare static RCD semantics. -/
theorem lg21ObservedAccessGaussianSource_reportRequiredActiveBranchProfile_nonempty
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature) :
    Nonempty (LG21ReportRequiredActiveBranchProfile source) := by
  rcases
      lg21ContinuousGaussianAccessPopulation_exists_reportRequiredSelfEnforcing_allTake
        source.population source.access_positive source.test_feature
        source.prior_variance_positive source.non_test_noise_variance_positive
        source.test_noise_variance_positive with
    ⟨candidate, htake⟩
  let selected := candidate.selected
  let hselection : LG21ReportRequiredFibrewiseActiveBranchSelection
      source.population source.access_positive source.test_feature selected
      candidate.source_timed :=
    { selected_self_enforcing := ⟨candidate, rfl⟩
      maximal_active_branch_ae := by
        dsimp [selected]
        intro other region hregion hpositive hcontains
        exact Filter.Eventually.of_forall fun student hother =>
          htake (lg21ContinuousPopulationSkill student)
            (lg21ContinuousPopulationBase source.test_feature student) }
  refine ⟨?_⟩
  exact
    { selected := selected
      positive_branch_pbo := candidate.source_timed
      active_branch_selection := hselection }

end

end LG21TestOptionalPolicies
