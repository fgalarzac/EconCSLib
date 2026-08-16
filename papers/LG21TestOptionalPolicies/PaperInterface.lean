import LG21TestOptionalPolicies.ContinuousPopulation
import LG21TestOptionalPolicies.Assumptions
import LG21TestOptionalPolicies.Definition1LiteralPBOContract
import LG21TestOptionalPolicies.ClarifiedTheorem32Model
import LG21TestOptionalPolicies.Theorem32GaussianCounterexample
import LG21TestOptionalPolicies.HiddenAccessTheorem31OptionalSourceCloseout
import LG21TestOptionalPolicies.HiddenAccessTheorem31LiteralOutputLawBridge
import LG21TestOptionalPolicies.HiddenAccessTheorem31ReportRequiredSourceCloseout
import LG21TestOptionalPolicies.HiddenAccessTheorem31ReportRequiredFairnessCloseout
import LG21TestOptionalPolicies.ObservedAccessLemma41LiteralSourceCloseout
import LG21TestOptionalPolicies.ObservedAccessOptionalSection4Bridge
import LG21TestOptionalPolicies.Proposition42ActiveBranchSourceBridge
import LG21TestOptionalPolicies.Proposition42ReportRequiredActiveBranchSourceBridge
import LG21TestOptionalPolicies.MandatoryObservedAccessProposition42Bridge
import LG21TestOptionalPolicies.MandatoryObservedAccessSection4PolicyEndpoints
import LG21TestOptionalPolicies.ObservedAccessAllProtocolD6OutputBridge
import LG21TestOptionalPolicies.MandatoryGivenAccessSection4Bridge
import LG21TestOptionalPolicies.ObservedAccessAllProtocolProposition43Bridge
import LG21TestOptionalPolicies.ObservedAccessAllProtocolTheorem44Fairness
import LG21TestOptionalPolicies.ObservedAccessProposition43PolicyEndpoints
import LG21TestOptionalPolicies.ObservedAccessPolicyTheorem44Endpoints
import LG21TestOptionalPolicies.MandatoryObservedAccessProposition43Nonvacuity
import LG21TestOptionalPolicies.MandatoryObservedAccessTheorem44FairnessBridge
import LG21TestOptionalPolicies.ObservedAccessVoluntaryActiveBranchCloseout
import LG21TestOptionalPolicies.ObservedAccessVoluntaryActiveBranchModels
import LG21TestOptionalPolicies.ObservedAccessOptionalActiveBranchSection4Bridge
import LG21TestOptionalPolicies.ObservedAccessReportRequiredActiveBranchSection4

/-!
# Paper Interface: LG21 Test-Optional Policies

This is the review surface for *Test-optional Policies: Overcoming Strategic
Behavior and Informational Gaps*. It states source-facing results in paper
order and keeps proof plumbing in implementation modules.

The source's literal arbitrary-randomized-policy version of Theorem 3.2 is
false. The approved clarified theorem below makes reported-score output
deterministic while retaining an arbitrary no-report law. The voluntary
Section 4 exposes declared source-timed, positive-mass self-enforcing
candidates and a fibrewise active-branch selection for the two voluntary
protocols. This makes the source's operational unraveling reading visible,
rather than claiming it follows from a literal static-RCD definition.
Legacy conditional Gaussian endpoints remain diagnostics. A null action fibre
is never assigned a fabricated payoff.

-/

namespace LG21TestOptionalPolicies

noncomputable section

open EconCSLib
open EconCSLib.Probability
open MeasureTheory
open ProbabilityTheory

namespace PaperInterface

/-! ## Source model and definitions -/

/-- The unit-mass continuous Gaussian student model with independent access. -/
abbrev student_gaussian_signal_model := @paper_student_gaussian_signal_model

/-- The source action constraints and access-independence model. -/
abbrev access_action_constraints_and_access_independence :=
  @paper_access_action_constraints_and_access_independence

/--
Definition 1 for the hidden-access optional protocol.  This is an explicit
source-timed contract: feasible actions, both decision-stage responses, and
the actual public/no-report PBO equations are all part of the proposition.
The no-report equality is guarded by its attained positive-mass event.
-/
abbrev definition1_hidden_access_optional_pbo_contract :=
  @LG21HiddenAccessOptionalPBODefinition1AE

/--
The literal hidden-access source carrier, with its score-stage response
obligation, realizes Definition 1's explicit PBO contract.  This is the
Definition 1 route used by the Section 3 theorems; it does not use the legacy
generic `estimationConsistent : Prop` field.
-/
theorem definition1_hidden_access_optional_source_timed
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (equilibrium : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hreport : equilibrium.OptionalReportBestResponseAE) :
    definition1_hidden_access_optional_pbo_contract equilibrium :=
  lg21HiddenAccessLiteralSourceEquilibriumAE_satisfies_definition1PBO
    equilibrium hreport

/--
Definition 1 for observed-access optional reporting under the documented
positive-mass operational reading.  It makes the source's `Z = 1, X = 0`
conditional-mean PBO explicit, conditions every unattained-branch statement
on positive mass, and keeps the two student decision times distinct.
-/
abbrev definition1_observed_access_optional_operational_pbo_contract :=
  @LG21ObservedAccessOptionalPBODefinition1Operational

/--
Every selected observed-access optional candidate used in the Section 4
closeout realizes the explicit operational Definition 1 contract.  The
contract contains feasibility, a.e. attained-branch responses, and actual
conditional-expectation PBO equations rather than an opaque consistency
placeholder.
-/
theorem definition1_observed_access_optional_operational_source_timed
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature}
    {haccess : 0 < M.accessLaw {true}} {testFeature : Feature}
    (candidate : LG21OptionalSourceTimedPositiveMassSelfEnforcingCandidate
      M haccess testFeature) :
    definition1_observed_access_optional_operational_pbo_contract candidate :=
  lg21OptionalSourceTimedPositiveMassSelfEnforcingCandidate_satisfies_definition1PBO
    candidate

/--
Definition 1 for observed-access reporting-required-after-taking under the
documented positive-mass operational reading. Taking remains a pre-score
choice; actual report and no-take conditional means are each guarded by their
own attained population.
-/
abbrev definition1_observed_access_report_required_operational_pbo_contract :=
  @LG21ObservedAccessReportRequiredPBODefinition1Operational

/--
The source-timed report-required candidate realizes feasibility, guarded
actual PBOs, and a.e. pre-score response/closure obligations without reading a
legacy opaque consistency field.
-/
abbrev definition1_observed_access_report_required_operational_source_timed :=
  @lg21ReportRequiredSourceTimedPositiveMassSelfEnforcingCandidate_satisfies_definition1PBO

/--
Definition 1 for reporting required given observed access. Feasibility fixes
the only access-side action, while the explicit contract records the actual
all-report and no-access PBO equations.
-/
abbrev definition1_observed_access_mandatory_pbo_contract :=
  @LG21ObservedAccessMandatoryPBODefinition1

/--
The source Gaussian model constructs a mandatory-given-access Definition 1
PBO witness directly. The result supplies no hidden PBO assumption and no
discretionary access-side best-response placeholder.
-/
abbrev definition1_observed_access_mandatory_pbo_source_witness :=
  @lg21ContinuousGaussianPopulation_exists_mandatoryDefinition1PBO

/-- The optional protocol's source-timed positive-mass candidate. Its PBO,
response, and outsider-closure obligations apply only to attained branches. -/
abbrev voluntary_optional_self_enforcing_candidate :=
  @LG21OptionalSourceTimedPositiveMassSelfEnforcingCandidate

/-- The report-required protocol's source-timed positive-mass candidate. -/
abbrev voluntary_report_required_self_enforcing_candidate :=
  @LG21ReportRequiredSourceTimedPositiveMassSelfEnforcingCandidate

/--
Declared operational selection for optional reporting in Section 4. This is
the branch-maximal preservation rule used by the voluntary closeout. It ranges
over source-timed self-enforcing positive-mass candidates; it is not a
restatement or consequence of literal static-RCD Definition 1.
-/
abbrev voluntary_optional_active_branch_selection :=
  @LG21OptionalFibrewiseActiveBranchSelection

/--
Declared operational selection for report-required-after-taking in Section 4.
The selected source-PBO record and candidate-side response/closure evidence
are part of the rule, so action selection cannot be detached from the
positive-branch conditional-mean semantics.
-/
abbrev voluntary_report_required_active_branch_selection :=
  @LG21ReportRequiredFibrewiseActiveBranchSelection

/-- Common continuous-Gaussian source parameters used by the selected
voluntary Section 4 routes. -/
abbrev observed_access_gaussian_source := @LG21ObservedAccessGaussianSource

/-- A selected optional profile with its explicit active-branch convention. -/
abbrev optional_active_branch_profile := @LG21OptionalActiveBranchProfile

/-- A selected report-required profile, its positive-branch PBO record, and
its explicit active-branch convention. -/
abbrev report_required_active_branch_profile := @LG21ReportRequiredActiveBranchProfile

/-- Definition 2: access/no-access estimate-law equality conditional on skill. -/
abbrev definition2_latent_skill_fair :=
  @lg21SourceLawLatentSkillFair

/-- Definition 3: access/no-access estimate-law equality conditional on observables. -/
abbrev definition3_observable_fair :=
  @lg21SourceLawObservablyFair

/-- Definition 4: demographic access/no-access estimate-law equality. -/
abbrev definition4_demographic_fair :=
  @lg21SourceLawDemographicallyFair

/-- Definition 5: equality of base-only and full-feature estimate laws. -/
abbrev definition5_test_blank :=
  @lg21SourceLawTestBlank

/-- Latent-skill fairness implies observable, then demographic, fairness. -/
abbrev fairness_implication_chain :=
  @paper_continuous_fairness_implication_chain_of_kernel_mixtures

/-! ## Theorem 3.1: hidden access and strategic withholding -/

/--
The optional-reporting source endpoint. Its explicit inputs are one literal
Gaussian population, source-timed taking/reporting actions, their on-path
PBO/best-response semantics, and positive-mass local-entry stability. It
concludes all taking, the finite score cutoff a.e., and positive withholding.
-/
def theorem3_1_optional_reporting_source_timedSpec : Prop :=
  ∀ {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ))
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hreportBest : E.OptionalReportBestResponseAE)
    (hstable : LG21HiddenAccessSourceStableAgainstLocalCandidateEntry E hnoAccess),
    lg21ContinuousGaussianPopulationLaw M E.activeNoTakeEvent = 0 ∧
      (∀ᵐ publicScore ∂lg21HiddenAccessAccessBaseScoreLaw M testFeature,
        E.reportDecision publicScore.1 publicScore.2 =
          decide (affineCutoff
            (gaussianSignalPriorWeight baseVariance
              (M.noiseVariance testFeature : ℝ) * baseMean publicScore.1)
            (gaussianSignalWeight baseVariance
              (M.noiseVariance testFeature : ℝ))
            (E.noReportPayoff publicScore.1) ≤ publicScore.2)) ∧
      0 < lg21ContinuousGaussianPopulationLaw M
        (lg21HiddenAccessAccessNoReportEvent testFeature E.reportDecision)

theorem theorem3_1_optional_reporting_source_timed :
    theorem3_1_optional_reporting_source_timedSpec :=
  @lg21HiddenAccess_optional_sourceCloseout_of_literalSourceStability

/-- The same literal optional source equilibrium fails latent-skill fairness. -/
abbrev theorem3_1_optional_reporting_not_latent_skill_fair :=
  @lg21HiddenAccessOptionalLiteralOutputLawSurface_not_latentSkillFair_of_literalSourceStability

/-- The same literal optional source equilibrium fails observable fairness. -/
abbrev theorem3_1_optional_reporting_not_observably_fair :=
  @lg21HiddenAccessOptionalLiteralOutputLawSurface_not_observablyFair_of_literalSourceStability

/-- The same literal optional source equilibrium fails demographic fairness. -/
abbrev theorem3_1_optional_reporting_not_demographically_fair :=
  @lg21HiddenAccessOptionalLiteralOutputLawSurface_not_demographicallyFair_of_literalSourceStability

/--
The report-required source equilibrium has positive access/no-take mass under
the literal Gaussian factorization. This is the paper's strategic withholding
population, not an off-path payoff convention.
-/
abbrev theorem3_1_report_required_positive_withholding :=
  @LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE.optionalNoReport_positive_of_sourceGaussianFactor

/--
Under the source's positive-mass local-tail equilibrium stability, the
report-required taking action has a finite skill cutoff almost everywhere in
the literal base law.
-/
abbrev theorem3_1_report_required_finite_take_cutoff_ae :=
  @LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE.exists_finite_takeCutoff_ae_of_localTailStability

/--
The report-required branch of Theorem 3.1 under the literal source timing.
For every reviewed literal source equilibrium satisfying the source's
positive-mass local-tail stability condition, it derives both advertised
consequences: positive withholding and a finite latent-skill taking cutoff
almost everywhere on the original public-base law.
-/
def theorem3_1_report_required_source_timedSpec : Prop :=
  ∀ {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (equilibrium : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE
      M testFeature)
    (hnoAccess : 0 < M.accessLaw {false})
    (hstable : LG21ReportRequiredStableAgainstLocalTailEntry
      (M := M) (testFeature := testFeature) equilibrium.source.takeDecision)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)),
    (0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessOptionalNoReportEvent testFeature
        equilibrium.source.takeDecision equilibrium.source.reportDecision)) ∧
      (let skillKernel := gaussianLocationKernel
        baseMean hbaseMean baseVariance.toNNReal
       letI : IsMarkovKernel skillKernel := gaussianLocationKernel_isMarkov
        baseMean hbaseMean baseVariance.toNNReal
       ∀ᵐ publicBase ∂baseLaw,
        ∃ cutoff : ℝ,
          ∀ᵐ latentSkill ∂skillKernel publicBase,
            equilibrium.source.takeDecision latentSkill publicBase =
              decide (cutoff ≤ latentSkill))

theorem theorem3_1_report_required_source_timed :
    theorem3_1_report_required_source_timedSpec := by
  dsimp only [theorem3_1_report_required_source_timedSpec]
  intro Feature instFintype instDecidableEq M testFeature equilibrium hnoAccess
    hstable hpriorVariance hnonTestNoiseVariance htestNoiseVariance baseLaw
    instProbability baseMean hbaseMean baseVariance hbaseVariance hsourceFactor
  constructor
  · exact theorem3_1_report_required_positive_withholding equilibrium hnoAccess
      baseLaw baseMean hbaseMean baseVariance hbaseVariance htestNoiseVariance
      hsourceFactor
  · exact theorem3_1_report_required_finite_take_cutoff_ae equilibrium hnoAccess
      hstable hpriorVariance hnonTestNoiseVariance htestNoiseVariance baseLaw
      baseMean hbaseMean baseVariance hbaseVariance hsourceFactor

/-- The forced-report literal actual-output surface fails Definition 2. -/
abbrev theorem3_1_report_required_not_latent_skill_fair :=
  @lg21HiddenAccessReportRequiredLiteralOutputLawSurface_not_latentSkillFair_of_sourceGaussianFactor

/-- The forced-report literal actual-output surface fails Definition 3. -/
abbrev theorem3_1_report_required_not_observably_fair :=
  @lg21HiddenAccessReportRequiredLiteralOutputLawSurface_not_observablyFair_of_sourceGaussianFactor

/-- The forced-report literal actual-output surface fails Definition 4. -/
abbrev theorem3_1_report_required_not_demographically_fair :=
  @lg21HiddenAccessReportRequiredLiteralOutputLawSurface_not_demographicallyFair_of_sourceGaussianFactor

/-- Combined actual-output-law closeout for the three source fairness notions. -/
abbrev theorem3_1_report_required_not_fair :=
  @lg21HiddenAccessReportRequiredLiteralOutputLawSurface_not_fair_of_sourceGaussianFactor

/--
The fairness-failure conclusion of Theorem 3.1, stated once for the two
source requirement regimes. The optional and report-required equilibrium
records are independently quantified literal source equilibria for their
respective timing rules. Each schedule-local implication is derived from its
own actual public-output laws; no fairness inequality or companion schedule
is supplied as an input.
-/
def theorem3_1_hidden_access_pbo_fails_all_fairness_definitionsSpec : Prop :=
  ∀ {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)),
    (∀ (optional : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature),
      optional.OptionalReportBestResponseAE →
        LG21HiddenAccessSourceStableAgainstLocalCandidateEntry optional hnoAccess →
        ¬ lg21SourceLawLatentSkillFair
        (lg21HiddenAccessOptionalLiteralOutputLawSurface
          M testFeature baseMean hbaseMean baseVariance) ∧
        ¬ lg21SourceLawObservablyFair
          (lg21HiddenAccessOptionalLiteralOutputLawSurface
            M testFeature baseMean hbaseMean baseVariance) ∧
        ¬ lg21SourceLawDemographicallyFair
          (lg21HiddenAccessOptionalLiteralOutputLawSurface
            M testFeature baseMean hbaseMean baseVariance)) ∧
      (∀ (reportRequired :
          LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature),
        LG21ReportRequiredStableAgainstLocalTailEntry
            (M := M) (testFeature := testFeature) reportRequired.source.takeDecision →
        ¬ lg21SourceLawLatentSkillFair
          (lg21HiddenAccessReportRequiredLiteralOutputLawSurface
            M testFeature baseMean hbaseMean baseVariance) ∧
        ¬ lg21SourceLawObservablyFair
          (lg21HiddenAccessReportRequiredLiteralOutputLawSurface
            M testFeature baseMean hbaseMean baseVariance) ∧
        ¬ lg21SourceLawDemographicallyFair
          (lg21HiddenAccessReportRequiredLiteralOutputLawSurface
            M testFeature baseMean hbaseMean baseVariance))

theorem theorem3_1_hidden_access_pbo_fails_all_fairness_definitions :
    theorem3_1_hidden_access_pbo_fails_all_fairness_definitionsSpec := by
  dsimp only [theorem3_1_hidden_access_pbo_fails_all_fairness_definitionsSpec]
  intro Feature instFintype instDecidableEq M haccess hnoAccess testFeature
    hpriorVariance hnonTestNoiseVariance htestNoiseVariance baseLaw instProbability
    baseMean hbaseMean baseVariance hbaseVariance hsourceFactor
  refine ⟨?_, ?_⟩
  · intro optional hoptionalReportBest hoptionalStable
    exact ⟨
      theorem3_1_optional_reporting_not_latent_skill_fair M haccess hnoAccess
        testFeature hpriorVariance hnonTestNoiseVariance htestNoiseVariance
        baseLaw baseMean hbaseMean baseVariance hbaseVariance hsourceFactor optional
        hoptionalReportBest hoptionalStable,
      theorem3_1_optional_reporting_not_observably_fair M haccess hnoAccess
        testFeature hpriorVariance hnonTestNoiseVariance htestNoiseVariance
        baseLaw baseMean hbaseMean baseVariance hbaseVariance hsourceFactor optional
        hoptionalReportBest hoptionalStable,
      theorem3_1_optional_reporting_not_demographically_fair M haccess hnoAccess
        testFeature hpriorVariance hnonTestNoiseVariance htestNoiseVariance
        baseLaw baseMean hbaseMean baseVariance hbaseVariance hsourceFactor optional
        hoptionalReportBest hoptionalStable⟩
  · intro reportRequired hreportRequiredStable
    exact theorem3_1_report_required_not_fair reportRequired hnoAccess
      hreportRequiredStable hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance baseLaw baseMean hbaseMean baseVariance hbaseVariance
      hsourceFactor

/--
Corrected support formula for the source's no-report mixture bookkeeping. It
is auxiliary correction evidence, not an additional named Theorem 3.1 target.
-/
theorem theorem3_1_corrected_no_report_mixture_formula
    (accessFraction baseOnlyEstimate : ℝ)
    (scoreLaw : GaussianScaleLaw)
    (accessLowerTailEstimate : ℝ → ℝ) (cutoff : ℝ) :
    lg21OptionalNoReportMixtureEstimate accessFraction baseOnlyEstimate
        scoreLaw accessLowerTailEstimate cutoff =
      ((1 - accessFraction) * baseOnlyEstimate +
          accessFraction * standardGaussianCDFAPI.normalCDF scoreLaw cutoff *
            accessLowerTailEstimate cutoff) /
        ((1 - accessFraction) +
          accessFraction * standardGaussianCDFAPI.normalCDF scoreLaw cutoff) := rfl

/-! ## Theorem 3.2: clarified deterministic-reporter theorem -/

/--
Archival diagnostic: arbitrary randomized output invalidates literal Theorem
3.2. It is not the governing clarified target.
-/
abbrev theorem3_2_gaussian_randomized_policy_counterexample :=
  @paper_theorem3_2_gaussian_randomized_policy_counterexample

/--
Clarified optional-reporting Theorem 3.2. Deterministic reported-score output
and latent-skill or observable fairness imply operational test blankness.
-/
def theorem3_2_optional_reporting_clarified_modelSpec : Prop :=
  ∀ {Base : Type*} [MeasurableSpace Base]
    (model : LG21ClarifiedOptionalReportingModel Base)
    (hFair : lg21SourceLawLatentSkillFair model.policy \/
      lg21SourceLawObservablyFair model.policy),
    ∀ e base,
      LG21OptionalOperationalTestBlank
        (model.scoreLaw e base)
        (model.policy.baseOnlyLaw e base)
        (model.reporterSet e base)
        (lg21OptionalDeterministicReporterKernel
          (model.reporterSet e base)
          (model.reporterSet_measurable e base)
          (model.reporterOutput e base)
          (model.reporterOutput_measurable e base)
          (model.policy.baseOnlyLaw e base))

theorem theorem3_2_optional_reporting_clarified_model :
    theorem3_2_optional_reporting_clarified_modelSpec := by
  dsimp only [theorem3_2_optional_reporting_clarified_modelSpec]
  intro Base instMeasurableSpace model hFair e base
  exact LG21ClarifiedOptionalReportingModel.operationalTestBlank_of_latent_or_observable
    model hFair e base

/--
Clarified report-required Theorem 3.2. Its Gaussian analytic step is proved;
the no-take output law remains arbitrary.
-/
def theorem3_2_report_required_clarified_modelSpec : Prop :=
  ∀ {Base : Type*} [MeasurableSpace Base]
    (model : LG21ClarifiedReportRequiredModel Base)
    (hFair : lg21SourceLawLatentSkillFair model.policy \/
      lg21SourceLawObservablyFair model.policy),
    ∀ e base, model.operationalTestBlank e base

theorem theorem3_2_report_required_clarified_model :
    theorem3_2_report_required_clarified_modelSpec := by
  dsimp only [theorem3_2_report_required_clarified_modelSpec]
  intro Base instMeasurableSpace model hFair e base
  exact LG21ClarifiedReportRequiredModel.operationalTestBlank_of_latent_or_observable
    model hFair e base

/-! ## Lemma 4.1: observed-access strategy-proofness -/

/--
The mandatory-given-access protocol is direct: source feasibility forces every
access action to be `takeAndReport`, and the same literal finite Gaussian
population supplies the Definition 6 resampling experiment.
-/
abbrev lemma4_1_mandatory_given_access_literal_source :=
  @lg21_mandatoryGivenAccess_literal_source_closeout

/--
Conditional all-protocol unraveling support. This consumes the legacy
one-direction entry carriers and therefore does not establish the source
Lemma 4.1 equilibrium claim: it has neither a nonvacuity witness nor the
two-sided closed-profile obligations needed for voluntary exits. It remains a
local analytic diagnostic while that source bridge is repaired.
-/
abbrev lemma4_1_all_observed_access_protocols_conditional_unraveling :=
  @lg21ContinuousGaussianAccessPopulation_lemma4_1_all_protocols_of_sourceTimed

/-- Lemma 4.1's mandatory-given-access branch. Feasibility itself forces the
attained access action, independently of either voluntary protocol. -/
theorem lemma4_1_mandatory_given_access_active_branch_selection
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (mandatory : LG21MandatoryGivenAccessLiteralSourceEquilibrium source.population) :
    ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw source.population,
      mandatory.action student = LG21AccessAction.takeAndReport := by
  exact lg21MandatoryGivenAccess_accessPopulation_ae_takeAndReport
    source.population source.access_positive mandatory.action mandatory.feasible

/-- Lemma 4.1's optional-reporting branch under the declared fibrewise
active-branch convention. Its conclusion is only almost everywhere, and the
selection is not claimed to follow from literal static-RCD Definition 1. -/
theorem lemma4_1_optional_active_branch_selection
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (profile : LG21OptionalActiveBranchProfile source) :
    ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw source.population,
      profile.selected.actions.takeDecision
          (lg21ContinuousPopulationSkill student)
          (lg21ContinuousPopulationBase source.test_feature student) = true ∧
        profile.selected.actions.reportDecision
          (lg21ContinuousPopulationBase source.test_feature student)
          (lg21ContinuousPopulationFeature source.test_feature student) = true := by
  exact
    lg21ContinuousGaussianAccessPopulation_optional_allTakeAllReport_of_fibrewiseActiveBranchSelection
      source.population source.access_positive source.test_feature
      source.prior_variance_positive source.non_test_noise_variance_positive
      source.test_noise_variance_positive profile.selected
      profile.active_branch_selection

/-- Lemma 4.1's report-required-after-taking branch under the declared
fibrewise active-branch convention and its coupled positive-branch PBO record.
No payoff is defined for the null no-take branch. -/
theorem lemma4_1_report_required_active_branch_selection
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (profile : LG21ReportRequiredActiveBranchProfile source) :
    ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw source.population,
      profile.selected.takeDecision
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase source.test_feature student) = true := by
  exact
    lg21ContinuousGaussianAccessPopulation_reportRequired_allTake_of_fibrewiseActiveBranchSelection
      source.population source.access_positive source.test_feature
      source.prior_variance_positive source.non_test_noise_variance_positive
      source.test_noise_variance_positive profile.selected
      profile.positive_branch_pbo profile.active_branch_selection

/-- The mandatory protocol's source-relevant action is unique on the access
population. This is action-profile uniqueness, not a claim about arbitrary
off-path conditional distributions. -/
theorem lemma4_1_mandatory_action_unique_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (left right : LG21MandatoryGivenAccessLiteralSourceEquilibrium source.population) :
    ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw source.population,
      left.action student = right.action student := by
  filter_upwards [
    lemma4_1_mandatory_given_access_active_branch_selection source left,
    lemma4_1_mandatory_given_access_active_branch_selection source right] with
      student hleft hright
  rw [hleft, hright]

/-- Under the declared selection, two optional profiles agree on the displayed
take/report actions almost everywhere. This is the precise continuous-model
reading of the source's displayed strategy uniqueness; it does not identify
null-branch PBO versions or unrelated policy values. -/
theorem lemma4_1_optional_actions_unique_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (left right : LG21OptionalActiveBranchProfile source) :
    ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw source.population,
      left.selected.actions.takeDecision
          (lg21ContinuousPopulationSkill student)
          (lg21ContinuousPopulationBase source.test_feature student) =
        right.selected.actions.takeDecision
          (lg21ContinuousPopulationSkill student)
          (lg21ContinuousPopulationBase source.test_feature student) ∧
      left.selected.actions.reportDecision
          (lg21ContinuousPopulationBase source.test_feature student)
          (lg21ContinuousPopulationFeature source.test_feature student) =
        right.selected.actions.reportDecision
          (lg21ContinuousPopulationBase source.test_feature student)
          (lg21ContinuousPopulationFeature source.test_feature student) := by
  filter_upwards [
    lemma4_1_optional_active_branch_selection source left,
    lemma4_1_optional_active_branch_selection source right] with student hleft hright
  exact ⟨by rw [hleft.1, hright.1], by rw [hleft.2, hright.2]⟩

/-- Under the declared selection, two report-required profiles agree on the
source-relevant taking action almost everywhere. As with the optional route,
this deliberately does not assert equality of null-branch PBO versions. -/
theorem lemma4_1_report_required_actions_unique_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (left right : LG21ReportRequiredActiveBranchProfile source) :
    ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw source.population,
      left.selected.takeDecision
          (lg21ContinuousPopulationSkill student)
          (lg21ContinuousPopulationBase source.test_feature student) =
        right.selected.takeDecision
          (lg21ContinuousPopulationSkill student)
          (lg21ContinuousPopulationBase source.test_feature student) := by
  filter_upwards [
    lemma4_1_report_required_active_branch_selection source left,
    lemma4_1_report_required_active_branch_selection source right] with
      student hleft hright
  rw [hleft, hright]

/--
Lemma 4.1 under the declared Section 4 operational convention. The three
universal fields keep the source's requirement regimes separate: mandatory
actions are feasible by construction, while the voluntary actions arise from
source-timed positive-mass profiles selected by the fibrewise maximal
active-branch rule. The remaining fields state the source-relevant action
uniqueness almost everywhere. This does not identify static-RCD null-branch
versions, PBO records, or arbitrary raw Definition 1 equilibria.
-/
def lemma4_1_observed_access_strategy_proofnessSpec : Prop :=
  ∀ {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature),
    Nonempty (LG21OptionalActiveBranchProfile source) ∧
      Nonempty (LG21ReportRequiredActiveBranchProfile source) ∧
      (∀ mandatory : LG21MandatoryGivenAccessLiteralSourceEquilibrium source.population,
      ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw source.population,
        mandatory.action student = LG21AccessAction.takeAndReport) ∧
      (∀ optionalProfile : LG21OptionalActiveBranchProfile source,
        ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw source.population,
          optionalProfile.selected.actions.takeDecision
              (lg21ContinuousPopulationSkill student)
              (lg21ContinuousPopulationBase source.test_feature student) = true ∧
            optionalProfile.selected.actions.reportDecision
              (lg21ContinuousPopulationBase source.test_feature student)
              (lg21ContinuousPopulationFeature source.test_feature student) = true) ∧
      (∀ reportRequiredProfile : LG21ReportRequiredActiveBranchProfile source,
        ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw source.population,
          reportRequiredProfile.selected.takeDecision
              (lg21ContinuousPopulationSkill student)
              (lg21ContinuousPopulationBase source.test_feature student) = true) ∧
      (∀ left right : LG21OptionalActiveBranchProfile source,
        ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw source.population,
          left.selected.actions.takeDecision
              (lg21ContinuousPopulationSkill student)
              (lg21ContinuousPopulationBase source.test_feature student) =
            right.selected.actions.takeDecision
              (lg21ContinuousPopulationSkill student)
              (lg21ContinuousPopulationBase source.test_feature student) ∧
          left.selected.actions.reportDecision
              (lg21ContinuousPopulationBase source.test_feature student)
              (lg21ContinuousPopulationFeature source.test_feature student) =
            right.selected.actions.reportDecision
              (lg21ContinuousPopulationBase source.test_feature student)
              (lg21ContinuousPopulationFeature source.test_feature student)) ∧
      ∀ left right : LG21ReportRequiredActiveBranchProfile source,
        ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw source.population,
          left.selected.takeDecision
              (lg21ContinuousPopulationSkill student)
              (lg21ContinuousPopulationBase source.test_feature student) =
            right.selected.takeDecision
              (lg21ContinuousPopulationSkill student)
              (lg21ContinuousPopulationBase source.test_feature student)

theorem lemma4_1_observed_access_strategy_proofness :
    lemma4_1_observed_access_strategy_proofnessSpec := by
  dsimp only [lemma4_1_observed_access_strategy_proofnessSpec]
  intro Feature instFintype instDecidableEq source
  exact ⟨
    lg21ObservedAccessGaussianSource_optionalActiveBranchProfile_nonempty source,
    lg21ObservedAccessGaussianSource_reportRequiredActiveBranchProfile_nonempty source,
    fun mandatory =>
      lemma4_1_mandatory_given_access_active_branch_selection source mandatory,
    fun optionalProfile =>
      lemma4_1_optional_active_branch_selection source optionalProfile,
    fun reportRequiredProfile =>
      lemma4_1_report_required_active_branch_selection source reportRequiredProfile,
    fun left right => lemma4_1_optional_actions_unique_ae source left right,
    fun left right => lemma4_1_report_required_actions_unique_ae source left right⟩

/--
The paper-facing core of Lemma 4.1. This retains every universal action and
almost-everywhere uniqueness conclusion while leaving profile construction to
the stronger aggregate theorem above.
-/
def lemma4_1_observed_access_strategy_proofness_source_coreSpec : Prop :=
  ∀ {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature),
    (∀ mandatory : LG21MandatoryGivenAccessLiteralSourceEquilibrium source.population,
      ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw source.population,
        mandatory.action student = LG21AccessAction.takeAndReport) ∧
      (∀ optionalProfile : LG21OptionalActiveBranchProfile source,
        ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw source.population,
          optionalProfile.selected.actions.takeDecision
              (lg21ContinuousPopulationSkill student)
              (lg21ContinuousPopulationBase source.test_feature student) = true ∧
            optionalProfile.selected.actions.reportDecision
              (lg21ContinuousPopulationBase source.test_feature student)
              (lg21ContinuousPopulationFeature source.test_feature student) = true) ∧
      (∀ reportRequiredProfile : LG21ReportRequiredActiveBranchProfile source,
        ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw source.population,
          reportRequiredProfile.selected.takeDecision
              (lg21ContinuousPopulationSkill student)
              (lg21ContinuousPopulationBase source.test_feature student) = true) ∧
      (∀ left right : LG21OptionalActiveBranchProfile source,
        ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw source.population,
          left.selected.actions.takeDecision
              (lg21ContinuousPopulationSkill student)
              (lg21ContinuousPopulationBase source.test_feature student) =
            right.selected.actions.takeDecision
              (lg21ContinuousPopulationSkill student)
              (lg21ContinuousPopulationBase source.test_feature student) ∧
          left.selected.actions.reportDecision
              (lg21ContinuousPopulationBase source.test_feature student)
              (lg21ContinuousPopulationFeature source.test_feature student) =
            right.selected.actions.reportDecision
              (lg21ContinuousPopulationBase source.test_feature student)
              (lg21ContinuousPopulationFeature source.test_feature student)) ∧
      ∀ left right : LG21ReportRequiredActiveBranchProfile source,
        ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw source.population,
          left.selected.takeDecision
              (lg21ContinuousPopulationSkill student)
              (lg21ContinuousPopulationBase source.test_feature student) =
            right.selected.takeDecision
              (lg21ContinuousPopulationSkill student)
              (lg21ContinuousPopulationBase source.test_feature student)

theorem lemma4_1_observed_access_strategy_proofness_source_core :
    lemma4_1_observed_access_strategy_proofness_source_coreSpec := by
  dsimp only [lemma4_1_observed_access_strategy_proofness_source_coreSpec]
  intro Feature instFintype instDecidableEq source
  exact ⟨
    fun mandatory =>
      lemma4_1_mandatory_given_access_active_branch_selection source mandatory,
    fun optionalProfile =>
      lemma4_1_optional_active_branch_selection source optionalProfile,
    fun reportRequiredProfile =>
      lemma4_1_report_required_active_branch_selection source reportRequiredProfile,
    fun left right => lemma4_1_optional_actions_unique_ae source left right,
    fun left right => lemma4_1_report_required_actions_unique_ae source left right⟩

/-- Corrected local raw-score indifference equation used in the Lemma 4.1 proof. -/
abbrev lemma4_1_taking_indifference_affine_inverse :=
  @paper_lemma4_1_taking_indifference_affine_inverse

/-! ## Propositions 4.2--4.3: observed-access information gaps -/

/--
Proposition 4.2 under the declared voluntary active-branch convention. The
policy is arbitrary on no-access applicants but performs the source's Gaussian
PBO estimation after an observed score. For every selected voluntary profile,
the witness records that its source output realizes that PBO output almost
everywhere and that the canonical total representative fails Definition 2's
fixed-fibre equality. The two universal fields expose the optional and
report-required versions of the source's claim that the argument does not
depend on the students' strategy space. This is the continuous/RCD
interpretation of the source conditional laws; it does not claim pointwise
equality for an arbitrary null-fibre PBO version.
-/
theorem proposition4_2_observed_access_pbo_policy_not_latent_skill_fair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (noAccessEstimateKernel : Kernel
      (LG21NonTestFeature Feature source.test_feature -> ℝ) ℝ)
    [IsMarkovKernel noAccessEstimateKernel]
    : Nonempty (LG21OptionalActiveBranchProfile source) ∧
      Nonempty (LG21ReportRequiredActiveBranchProfile source) ∧
      (∀ optionalProfile : LG21OptionalActiveBranchProfile source,
        LG21P42OptionalActiveBranchCanonicalPolicyWitness source optionalProfile
          noAccessEstimateKernel) ∧
      ∀ reportRequiredProfile : LG21ReportRequiredActiveBranchProfile source,
        LG21P42ReportRequiredActiveBranchCanonicalPolicyWitness source
          reportRequiredProfile noAccessEstimateKernel := by
  exact ⟨
    lg21ObservedAccessGaussianSource_optionalActiveBranchProfile_nonempty source,
    lg21ObservedAccessGaussianSource_reportRequiredActiveBranchProfile_nonempty source,
    fun optionalProfile =>
      lg21P42_optionalActiveBranchCanonicalPolicy_not_latent_skill_fair source
        optionalProfile noAccessEstimateKernel,
    fun reportRequiredProfile =>
      lg21P42_reportRequiredActiveBranchCanonicalPolicy_not_latent_skill_fair
        source reportRequiredProfile noAccessEstimateKernel⟩

/--
Proposition 4.2 for reporting required given access, the third observed-access
protocol. The profile contains the literal mandatory action and the actual
all-report PBO condition. For every arbitrary base-only no-access policy, the
source-derived full-base Gaussian experiment supplies an a.e. realization of
the canonical fixed-fibre policy whose exact Definition 2 conclusion is not
latent-skill fairness. No access/output-law equality is a premise.
-/
theorem proposition4_2_mandatory_given_access_pbo_policy_not_latent_skill_fair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (noAccessEstimateKernel : Kernel
      (LG21NonTestFeature Feature source.test_feature -> ℝ) ℝ)
    [IsMarkovKernel noAccessEstimateKernel] :
    Nonempty (LG21P42MandatoryGivenAccessPBOProfile source) ∧
      ∀ mandatoryProfile : LG21P42MandatoryGivenAccessPBOProfile source,
        LG21P42MandatoryGivenAccessCanonicalPolicyWitness source
          mandatoryProfile noAccessEstimateKernel := by
  exact ⟨
    lg21P42MandatoryGivenAccessPBOProfile_nonempty source,
    fun mandatoryProfile =>
      lg21P42_mandatoryGivenAccessCanonicalPolicy_not_latent_skill_fair source
        mandatoryProfile noAccessEstimateKernel⟩

/--
Proposition 4.2 across the three requirement policies advertised by the source.
Each conjunct retains its own protocol-specific profile quantifier; the theorem
does not require a shared profile, an equality of off-path outputs, or any
cross-protocol stability premise.
-/
def proposition4_2_all_observed_access_requirement_protocolsSpec : Prop :=
  ∀ {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (noAccessEstimateKernel : Kernel
      (LG21NonTestFeature Feature source.test_feature -> ℝ) ℝ)
    [IsMarkovKernel noAccessEstimateKernel],
    (Nonempty (LG21OptionalActiveBranchProfile source) ∧
      Nonempty (LG21ReportRequiredActiveBranchProfile source) ∧
      (∀ optionalProfile : LG21OptionalActiveBranchProfile source,
        LG21P42OptionalActiveBranchCanonicalPolicyWitness source optionalProfile
          noAccessEstimateKernel) ∧
      ∀ reportRequiredProfile : LG21ReportRequiredActiveBranchProfile source,
        LG21P42ReportRequiredActiveBranchCanonicalPolicyWitness source
          reportRequiredProfile noAccessEstimateKernel) ∧
    (Nonempty (LG21P42MandatoryGivenAccessPBOProfile source) ∧
      ∀ mandatoryProfile : LG21P42MandatoryGivenAccessPBOProfile source,
        LG21P42MandatoryGivenAccessCanonicalPolicyWitness source
          mandatoryProfile noAccessEstimateKernel)

theorem proposition4_2_all_observed_access_requirement_protocols :
    proposition4_2_all_observed_access_requirement_protocolsSpec := by
  dsimp only [proposition4_2_all_observed_access_requirement_protocolsSpec]
  intro Feature instFintype instDecidableEq source noAccessEstimateKernel
    instMarkovKernel
  exact ⟨
    proposition4_2_observed_access_pbo_policy_not_latent_skill_fair source
      noAccessEstimateKernel,
    proposition4_2_mandatory_given_access_pbo_policy_not_latent_skill_fair source
      noAccessEstimateKernel⟩

/--
The paper-facing core of Proposition 4.2. It quantifies over every profile in
each requirement regime and retains each latent-skill-fairness failure, without
packaging separate profile-existence witnesses into the claimed conclusion.
-/
def proposition4_2_all_observed_access_requirement_protocols_source_coreSpec : Prop :=
  ∀ {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (noAccessEstimateKernel : Kernel
      (LG21NonTestFeature Feature source.test_feature -> ℝ) ℝ)
    [IsMarkovKernel noAccessEstimateKernel],
    ((∀ optionalProfile : LG21OptionalActiveBranchProfile source,
        LG21P42OptionalActiveBranchCanonicalPolicyWitness source optionalProfile
          noAccessEstimateKernel) ∧
      ∀ reportRequiredProfile : LG21ReportRequiredActiveBranchProfile source,
        LG21P42ReportRequiredActiveBranchCanonicalPolicyWitness source
          reportRequiredProfile noAccessEstimateKernel) ∧
    ∀ mandatoryProfile : LG21P42MandatoryGivenAccessPBOProfile source,
      LG21P42MandatoryGivenAccessCanonicalPolicyWitness source
        mandatoryProfile noAccessEstimateKernel

theorem proposition4_2_all_observed_access_requirement_protocols_source_core :
    proposition4_2_all_observed_access_requirement_protocols_source_coreSpec := by
  dsimp only [proposition4_2_all_observed_access_requirement_protocols_source_coreSpec]
  intro Feature instFintype instDecidableEq source noAccessEstimateKernel
    instMarkovKernel
  have voluntary :=
    proposition4_2_observed_access_pbo_policy_not_latent_skill_fair source
      noAccessEstimateKernel
  have mandatory :=
    proposition4_2_mandatory_given_access_pbo_policy_not_latent_skill_fair source
      noAccessEstimateKernel
  exact ⟨voluntary.2.2, mandatory.2⟩

/--
Conditional optional actual-output gaps for the Proposition 4.3 calculation.
This is analytic support; the direct active-branch endpoints below supply the
source-facing voluntary routes under the recorded operational convention.
-/
abbrev proposition4_3_conditional_optional_source_timed :=
  @lg21ContinuousGaussianPopulation_optional_sourceTimed_proposition43_actual_gaps

/-- The mandatory Gaussian source construction has the Proposition 4.3 gaps. -/
abbrev proposition4_3_mandatory_source :=
  @LG21MandatorySection4Source.proposition43_mandatory_actual_measure_gaps

/--
Nonvacuous mandatory-given-access witness for the Proposition 4.3 calculation.
Feasibility fixes the access action, so this route does not rely on a voluntary
null-branch equilibrium convention.
-/
abbrev proposition4_3_mandatory_given_access_nonvacuity :=
  @lg21ContinuousGaussianPopulation_mandatory_actualPBO_not_fair_exists_literalSource

/--
Proposition 4.3 for reporting required given access.  The actual Gaussian
source has a mandatory Definition 1 PBO profile, and every such profile fails
both paper fairness predicates.  The unreachable access/no-report output is
universally quantified, not supplied as an equilibrium assumption.
-/
theorem proposition4_3_mandatory_given_access_pbo_not_observable_or_demographic_fair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (hnoAccess : 0 < source.population.accessLaw {false}) :
    Nonempty (LG21P43MandatoryGivenAccessPBOProfile source hnoAccess) ∧
      ∀ (profile : LG21P43MandatoryGivenAccessPBOProfile source hnoAccess)
        (noReportPayoff :
          (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ),
        LG21P43MandatoryGivenAccessFairnessFailure source hnoAccess profile
          noReportPayoff := by
  exact lg21P43_mandatoryGivenAccess_actualPBO_nonempty_and_not_fair source hnoAccess

/--
Optional-reporting Proposition 4.3 route under the declared active-branch
selection. It packages the attained access PBO output and literal no-access
PBO output as one access-dispatched policy, and refutes both fairness
definitions for that policy.
-/
theorem proposition4_3_optional_active_branch_selection
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (profile : LG21OptionalActiveBranchProfile source)
    (hnoAccess : 0 < source.population.accessLaw {false})
    (noAccessOutput : Bool × (ℝ × (Feature -> ℝ)) -> ℝ)
    (hnoAccessPBO : LG21ContinuousGaussianNoAccessPopulationPBO
      source.population hnoAccess source.test_feature noAccessOutput) :
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianAccessPopulationLaw source.population) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability source.population
        source.access_positive
    letI : IsFiniteMeasure
        (lg21ContinuousGaussianAccessPopulationLaw source.population) := ⟨by simp⟩
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianNoAccessPopulationLaw source.population) :=
      lg21ContinuousGaussianNoAccessPopulationLaw_isProbability source.population
        hnoAccess
    letI : IsFiniteMeasure
        (lg21ContinuousGaussianNoAccessPopulationLaw source.population) := ⟨by simp⟩
    ∃ (baseLaw : Measure (LG21NonTestFeature Feature source.test_feature -> ℝ))
        (baseMean : (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ)
        (baseVariance baseMeanVariance : ℝ)
        (hbaseLaw : IsProbabilityMeasure baseLaw)
        (hbaseMean : Measurable baseMean)
        (hbaseVariance : 0 < baseVariance),
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw source.population
          source.test_feature =
          baseLaw ⊗ₘ gaussianLocationKernel
            baseMean hbaseMean baseVariance.toNNReal ∧
        0 ≤ baseMeanVariance ∧
        (¬ LG21ObservedAccessDeterministicObservableFairAE baseLaw
            (lg21ContinuousPopulationBase source.test_feature)
            (lg21ContinuousGaussianAccessPopulationLaw source.population)
            (lg21ContinuousGaussianNoAccessPopulationLaw source.population)
            (lg21ObservedAccessDeterministicTwoBranchOutput
              lg21ContinuousPopulationAccess
              (lg21OptionalSourceTimedActualOutput
                (lg21ContinuousPopulationBase source.test_feature)
                (lg21ContinuousPopulationFeature source.test_feature)
                (lg21ContinuousPopulationSkill (Feature := Feature))
                profile.selected.actions)
              noAccessOutput)) ∧
          (¬ LG21ObservedAccessDeterministicDemographicallyFair
            (lg21ContinuousGaussianAccessPopulationLaw source.population)
            (lg21ContinuousGaussianNoAccessPopulationLaw source.population)
            (lg21ObservedAccessDeterministicTwoBranchOutput
              lg21ContinuousPopulationAccess
              (lg21OptionalSourceTimedActualOutput
                (lg21ContinuousPopulationBase source.test_feature)
                (lg21ContinuousPopulationFeature source.test_feature)
                (lg21ContinuousPopulationSkill (Feature := Feature))
                profile.selected.actions)
              noAccessOutput)) := by
  exact
    lg21ContinuousGaussianPopulation_optional_activeBranchSelection_actualPBO_not_fair
      source.population source.access_positive hnoAccess source.test_feature
      source.prior_variance_positive source.non_test_noise_variance_positive
      source.test_noise_variance_positive profile.selected
      profile.active_branch_selection noAccessOutput hnoAccessPBO

/--
Report-required Proposition 4.3 route under the declared active-branch
selection and its coupled positive-branch source-PBO record. It makes the
same one-policy fairness refutations as the optional route without assigning
a null no-take payoff.
-/
theorem proposition4_3_report_required_active_branch_selection
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (profile : LG21ReportRequiredActiveBranchProfile source)
    (hnoAccess : 0 < source.population.accessLaw {false})
    (noAccessOutput : Bool × (ℝ × (Feature -> ℝ)) -> ℝ)
    (hnoAccessPBO : LG21ContinuousGaussianNoAccessPopulationPBO
      source.population hnoAccess source.test_feature noAccessOutput) :
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianAccessPopulationLaw source.population) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability source.population
        source.access_positive
    letI : IsFiniteMeasure
        (lg21ContinuousGaussianAccessPopulationLaw source.population) := ⟨by simp⟩
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianNoAccessPopulationLaw source.population) :=
      lg21ContinuousGaussianNoAccessPopulationLaw_isProbability source.population
        hnoAccess
    letI : IsFiniteMeasure
        (lg21ContinuousGaussianNoAccessPopulationLaw source.population) := ⟨by simp⟩
    ∃ (baseLaw : Measure (LG21NonTestFeature Feature source.test_feature -> ℝ))
        (baseMean : (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ)
        (baseVariance baseMeanVariance : ℝ)
        (hbaseLaw : IsProbabilityMeasure baseLaw)
        (hbaseMean : Measurable baseMean)
        (hbaseVariance : 0 < baseVariance),
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw source.population
          source.test_feature =
          baseLaw ⊗ₘ gaussianLocationKernel
            baseMean hbaseMean baseVariance.toNNReal ∧
        0 ≤ baseMeanVariance ∧
        (¬ LG21ObservedAccessDeterministicObservableFairAE baseLaw
            (lg21ContinuousPopulationBase source.test_feature)
            (lg21ContinuousGaussianAccessPopulationLaw source.population)
            (lg21ContinuousGaussianNoAccessPopulationLaw source.population)
            (lg21ObservedAccessDeterministicTwoBranchOutput
              lg21ContinuousPopulationAccess
              (lg21ReportRequiredSequentialActualOutput
                (lg21ContinuousPopulationBase source.test_feature)
                (lg21ContinuousPopulationFeature source.test_feature)
                (lg21ContinuousPopulationSkill (Feature := Feature)) profile.selected)
              noAccessOutput)) ∧
          (¬ LG21ObservedAccessDeterministicDemographicallyFair
            (lg21ContinuousGaussianAccessPopulationLaw source.population)
            (lg21ContinuousGaussianNoAccessPopulationLaw source.population)
            (lg21ObservedAccessDeterministicTwoBranchOutput
              lg21ContinuousPopulationAccess
              (lg21ReportRequiredSequentialActualOutput
                (lg21ContinuousPopulationBase source.test_feature)
                (lg21ContinuousPopulationFeature source.test_feature)
                (lg21ContinuousPopulationSkill (Feature := Feature)) profile.selected)
              noAccessOutput)) := by
  exact
    lg21ContinuousGaussianPopulation_reportRequired_activeBranchSelection_actualPBO_not_fair
      source.population source.access_positive hnoAccess source.test_feature
      source.prior_variance_positive source.non_test_noise_variance_positive
      source.test_noise_variance_positive profile.selected
      profile.positive_branch_pbo profile.active_branch_selection
      noAccessOutput hnoAccessPBO

/--
Proposition 4.3 under the declared voluntary active-branch convention. For
every selected optional or report-required profile, this packages the attained
access PBO and the literal no-access PBO as one access-dispatched policy and
refutes both paper fairness predicates for that policy. The two protocol
fields are independent rather than a simultaneous-profile premise; the
selected output laws are used only at their RCD-almost-everywhere scope.
-/
theorem proposition4_3_observed_access_pbo_not_observable_or_demographic_fair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (hnoAccess : 0 < source.population.accessLaw {false})
    (noAccessOutput : Bool × (ℝ × (Feature -> ℝ)) -> ℝ)
    (hnoAccessPBO : LG21ContinuousGaussianNoAccessPopulationPBO
      source.population hnoAccess source.test_feature noAccessOutput) :
    let claim : (Bool × (ℝ × (Feature -> ℝ)) -> ℝ) -> Prop :=
      fun actualOutput =>
        letI : IsProbabilityMeasure
            (lg21ContinuousGaussianAccessPopulationLaw source.population) :=
          lg21ContinuousGaussianAccessPopulationLaw_isProbability source.population
            source.access_positive
        letI : IsFiniteMeasure
            (lg21ContinuousGaussianAccessPopulationLaw source.population) := ⟨by simp⟩
        letI : IsProbabilityMeasure
            (lg21ContinuousGaussianNoAccessPopulationLaw source.population) :=
          lg21ContinuousGaussianNoAccessPopulationLaw_isProbability source.population
            hnoAccess
        letI : IsFiniteMeasure
            (lg21ContinuousGaussianNoAccessPopulationLaw source.population) := ⟨by simp⟩
        ∃ (baseLaw : Measure (LG21NonTestFeature Feature source.test_feature -> ℝ))
            (baseMean : (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ)
            (baseVariance baseMeanVariance : ℝ)
            (hbaseLaw : IsProbabilityMeasure baseLaw)
            (hbaseMean : Measurable baseMean)
            (hbaseVariance : 0 < baseVariance),
          lg21ContinuousGaussianFullBaseLatentPrimitiveLaw source.population
              source.test_feature =
              baseLaw ⊗ₘ gaussianLocationKernel
                baseMean hbaseMean baseVariance.toNNReal ∧
            0 ≤ baseMeanVariance ∧
            (¬ LG21ObservedAccessDeterministicObservableFairAE baseLaw
                (lg21ContinuousPopulationBase source.test_feature)
                (lg21ContinuousGaussianAccessPopulationLaw source.population)
                (lg21ContinuousGaussianNoAccessPopulationLaw source.population)
                (lg21ObservedAccessDeterministicTwoBranchOutput
                  lg21ContinuousPopulationAccess actualOutput noAccessOutput)) ∧
              (¬ LG21ObservedAccessDeterministicDemographicallyFair
                (lg21ContinuousGaussianAccessPopulationLaw source.population)
                (lg21ContinuousGaussianNoAccessPopulationLaw source.population)
                (lg21ObservedAccessDeterministicTwoBranchOutput
                  lg21ContinuousPopulationAccess actualOutput noAccessOutput))
    Nonempty (LG21OptionalActiveBranchProfile source) ∧
      Nonempty (LG21ReportRequiredActiveBranchProfile source) ∧
      (∀ optionalProfile : LG21OptionalActiveBranchProfile source,
        claim
          (lg21OptionalSourceTimedActualOutput
            (lg21ContinuousPopulationBase source.test_feature)
            (lg21ContinuousPopulationFeature source.test_feature)
            (lg21ContinuousPopulationSkill (Feature := Feature))
            optionalProfile.selected.actions)) ∧
      ∀ reportRequiredProfile : LG21ReportRequiredActiveBranchProfile source,
        claim
          (lg21ReportRequiredSequentialActualOutput
            (lg21ContinuousPopulationBase source.test_feature)
            (lg21ContinuousPopulationFeature source.test_feature)
            (lg21ContinuousPopulationSkill (Feature := Feature))
            reportRequiredProfile.selected) := by
  dsimp
  exact ⟨
    lg21ObservedAccessGaussianSource_optionalActiveBranchProfile_nonempty source,
    lg21ObservedAccessGaussianSource_reportRequiredActiveBranchProfile_nonempty source,
    fun optionalProfile =>
      proposition4_3_optional_active_branch_selection source optionalProfile
        hnoAccess noAccessOutput hnoAccessPBO,
    fun reportRequiredProfile =>
      proposition4_3_report_required_active_branch_selection source
        reportRequiredProfile hnoAccess noAccessOutput hnoAccessPBO⟩

/--
Proposition 4.3 across the three requirement policies advertised by the source.
The voluntary and mandatory PBOs remain independently quantified because their
attained information branches differ. In particular, this does not impose one
shared no-report output or an off-path completion across protocols.
-/
def proposition4_3_all_observed_access_requirement_protocolsSpec : Prop :=
  ∀ {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (hnoAccess : 0 < source.population.accessLaw {false})
    (noAccessOutput : Bool × (ℝ × (Feature -> ℝ)) -> ℝ)
    (hnoAccessPBO : LG21ContinuousGaussianNoAccessPopulationPBO
      source.population hnoAccess source.test_feature noAccessOutput),
    (let claim : (Bool × (ℝ × (Feature -> ℝ)) -> ℝ) -> Prop :=
      fun actualOutput =>
        letI : IsProbabilityMeasure
            (lg21ContinuousGaussianAccessPopulationLaw source.population) :=
          lg21ContinuousGaussianAccessPopulationLaw_isProbability source.population
            source.access_positive
        letI : IsFiniteMeasure
            (lg21ContinuousGaussianAccessPopulationLaw source.population) := ⟨by simp⟩
        letI : IsProbabilityMeasure
            (lg21ContinuousGaussianNoAccessPopulationLaw source.population) :=
          lg21ContinuousGaussianNoAccessPopulationLaw_isProbability source.population
            hnoAccess
        letI : IsFiniteMeasure
            (lg21ContinuousGaussianNoAccessPopulationLaw source.population) := ⟨by simp⟩
        ∃ (baseLaw : Measure (LG21NonTestFeature Feature source.test_feature -> ℝ))
            (baseMean : (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ)
            (baseVariance baseMeanVariance : ℝ)
            (hbaseLaw : IsProbabilityMeasure baseLaw)
            (hbaseMean : Measurable baseMean)
            (hbaseVariance : 0 < baseVariance),
          lg21ContinuousGaussianFullBaseLatentPrimitiveLaw source.population
              source.test_feature =
              baseLaw ⊗ₘ gaussianLocationKernel
                baseMean hbaseMean baseVariance.toNNReal ∧
            0 ≤ baseMeanVariance ∧
            (¬ LG21ObservedAccessDeterministicObservableFairAE baseLaw
                (lg21ContinuousPopulationBase source.test_feature)
                (lg21ContinuousGaussianAccessPopulationLaw source.population)
                (lg21ContinuousGaussianNoAccessPopulationLaw source.population)
                (lg21ObservedAccessDeterministicTwoBranchOutput
                  lg21ContinuousPopulationAccess actualOutput noAccessOutput)) ∧
              (¬ LG21ObservedAccessDeterministicDemographicallyFair
                (lg21ContinuousGaussianAccessPopulationLaw source.population)
                (lg21ContinuousGaussianNoAccessPopulationLaw source.population)
                (lg21ObservedAccessDeterministicTwoBranchOutput
                  lg21ContinuousPopulationAccess actualOutput noAccessOutput))
     Nonempty (LG21OptionalActiveBranchProfile source) ∧
      Nonempty (LG21ReportRequiredActiveBranchProfile source) ∧
      (∀ optionalProfile : LG21OptionalActiveBranchProfile source,
        claim
          (lg21OptionalSourceTimedActualOutput
            (lg21ContinuousPopulationBase source.test_feature)
            (lg21ContinuousPopulationFeature source.test_feature)
            (lg21ContinuousPopulationSkill (Feature := Feature))
            optionalProfile.selected.actions)) ∧
      ∀ reportRequiredProfile : LG21ReportRequiredActiveBranchProfile source,
        claim
          (lg21ReportRequiredSequentialActualOutput
            (lg21ContinuousPopulationBase source.test_feature)
            (lg21ContinuousPopulationFeature source.test_feature)
            (lg21ContinuousPopulationSkill (Feature := Feature))
            reportRequiredProfile.selected)) ∧
    (Nonempty (LG21P43MandatoryGivenAccessPBOProfile source hnoAccess) ∧
      ∀ (profile : LG21P43MandatoryGivenAccessPBOProfile source hnoAccess)
        (mandatoryNoReportPayoff :
          (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ),
        LG21P43MandatoryGivenAccessFairnessFailure source hnoAccess profile
          mandatoryNoReportPayoff)

theorem proposition4_3_all_observed_access_requirement_protocols :
    proposition4_3_all_observed_access_requirement_protocolsSpec := by
  dsimp only [proposition4_3_all_observed_access_requirement_protocolsSpec]
  intro Feature instFintype instDecidableEq source hnoAccess noAccessOutput
    hnoAccessPBO
  exact ⟨
    proposition4_3_observed_access_pbo_not_observable_or_demographic_fair source
      hnoAccess noAccessOutput hnoAccessPBO,
    proposition4_3_mandatory_given_access_pbo_not_observable_or_demographic_fair
      source hnoAccess⟩

/--
The paper-facing core of Proposition 4.3. It retains the observable- and
demographic-fairness failures for every voluntary and mandatory profile while
omitting only the stronger aggregate theorem's profile-existence packages.
-/
def proposition4_3_all_observed_access_requirement_protocols_source_coreSpec : Prop :=
  ∀ {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (hnoAccess : 0 < source.population.accessLaw {false})
    (noAccessOutput : Bool × (ℝ × (Feature -> ℝ)) -> ℝ)
    (hnoAccessPBO : LG21ContinuousGaussianNoAccessPopulationPBO
      source.population hnoAccess source.test_feature noAccessOutput),
    (let claim : (Bool × (ℝ × (Feature -> ℝ)) -> ℝ) -> Prop :=
      fun actualOutput =>
        letI : IsProbabilityMeasure
            (lg21ContinuousGaussianAccessPopulationLaw source.population) :=
          lg21ContinuousGaussianAccessPopulationLaw_isProbability source.population
            source.access_positive
        letI : IsFiniteMeasure
            (lg21ContinuousGaussianAccessPopulationLaw source.population) := ⟨by simp⟩
        letI : IsProbabilityMeasure
            (lg21ContinuousGaussianNoAccessPopulationLaw source.population) :=
          lg21ContinuousGaussianNoAccessPopulationLaw_isProbability source.population
            hnoAccess
        letI : IsFiniteMeasure
            (lg21ContinuousGaussianNoAccessPopulationLaw source.population) := ⟨by simp⟩
        ∃ (baseLaw : Measure (LG21NonTestFeature Feature source.test_feature -> ℝ))
            (baseMean : (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ)
            (baseVariance baseMeanVariance : ℝ)
            (hbaseLaw : IsProbabilityMeasure baseLaw)
            (hbaseMean : Measurable baseMean)
            (hbaseVariance : 0 < baseVariance),
          lg21ContinuousGaussianFullBaseLatentPrimitiveLaw source.population
              source.test_feature =
              baseLaw ⊗ₘ gaussianLocationKernel
                baseMean hbaseMean baseVariance.toNNReal ∧
            0 ≤ baseMeanVariance ∧
            (¬ LG21ObservedAccessDeterministicObservableFairAE baseLaw
                (lg21ContinuousPopulationBase source.test_feature)
                (lg21ContinuousGaussianAccessPopulationLaw source.population)
                (lg21ContinuousGaussianNoAccessPopulationLaw source.population)
                (lg21ObservedAccessDeterministicTwoBranchOutput
                  lg21ContinuousPopulationAccess actualOutput noAccessOutput)) ∧
              (¬ LG21ObservedAccessDeterministicDemographicallyFair
                (lg21ContinuousGaussianAccessPopulationLaw source.population)
                (lg21ContinuousGaussianNoAccessPopulationLaw source.population)
                (lg21ObservedAccessDeterministicTwoBranchOutput
                  lg21ContinuousPopulationAccess actualOutput noAccessOutput))
     (∀ optionalProfile : LG21OptionalActiveBranchProfile source,
        claim
          (lg21OptionalSourceTimedActualOutput
            (lg21ContinuousPopulationBase source.test_feature)
            (lg21ContinuousPopulationFeature source.test_feature)
            (lg21ContinuousPopulationSkill (Feature := Feature))
            optionalProfile.selected.actions)) ∧
      ∀ reportRequiredProfile : LG21ReportRequiredActiveBranchProfile source,
        claim
          (lg21ReportRequiredSequentialActualOutput
            (lg21ContinuousPopulationBase source.test_feature)
            (lg21ContinuousPopulationFeature source.test_feature)
            (lg21ContinuousPopulationSkill (Feature := Feature))
            reportRequiredProfile.selected)) ∧
    ∀ (profile : LG21P43MandatoryGivenAccessPBOProfile source hnoAccess)
      (mandatoryNoReportPayoff :
        (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ),
      LG21P43MandatoryGivenAccessFairnessFailure source hnoAccess profile
        mandatoryNoReportPayoff

theorem proposition4_3_all_observed_access_requirement_protocols_source_core :
    proposition4_3_all_observed_access_requirement_protocols_source_coreSpec := by
  dsimp only [proposition4_3_all_observed_access_requirement_protocols_source_coreSpec]
  intro Feature instFintype instDecidableEq source hnoAccess noAccessOutput
    hnoAccessPBO
  have voluntary :=
    proposition4_3_observed_access_pbo_not_observable_or_demographic_fair source
      hnoAccess noAccessOutput hnoAccessPBO
  have mandatory :=
    proposition4_3_mandatory_given_access_pbo_not_observable_or_demographic_fair
      source hnoAccess
  exact ⟨voluntary.2.2, mandatory.2⟩

/-- Corrected local direct marginal Gaussian comparison supporting Proposition 4.3. -/
abbrev proposition4_3_actual_gaussian_measure_repair :=
  @paper_proposition4_3_actual_gaussian_measure_observable_and_demographic_gaps

/--
Internal simultaneous aggregation of the three independently useful
Proposition 4.3 routes.  It is not the paper-facing route: requiring all
three protocol carriers together would weaken the source's per-protocol
claim.  The direct independent endpoints follow below.
-/
theorem proposition4_3_simultaneous_protocols_auxiliary
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (mandatory : LG21MandatoryGivenAccessLiteralSourceEquilibrium M)
    (mandatoryReportedPayoff :
      (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> ℝ)
    (mandatoryNoReportPayoff :
      (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hmandatoryReportedPBO : LG21ObservedAccessAllReportPBO
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) mandatoryReportedPayoff)
    (optional : LG21ObservedAccessOptionalSourceTimedEquilibrium
      M haccess testFeature)
    (reportRequired : LG21ReportRequiredSequentialEquilibriumData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    (hreportRequiredTestLaw : ∀ latentSkill publicBase,
      reportRequired.testLaw latentSkill publicBase = gaussianReal latentSkill
        ((M.noiseVariance testFeature : ℝ).toNNReal))
    (noAccessOutput : Bool × (ℝ × (Feature -> ℝ)) -> ℝ)
    (hnoAccessPBO : LG21ContinuousGaussianNoAccessPopulationPBO
      M hnoAccess testFeature noAccessOutput) :
    letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    letI : IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
    letI : IsProbabilityMeasure (lg21ContinuousGaussianNoAccessPopulationLaw M) :=
      lg21ContinuousGaussianNoAccessPopulationLaw_isProbability M hnoAccess
    letI : IsFiniteMeasure (lg21ContinuousGaussianNoAccessPopulationLaw M) := ⟨by simp⟩
    ∀ (reportRequiredSource : LG21FullPublicReportRequiredSourceEquilibrium
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired),
      LG21ReportRequiredSourceStableAgainstPositiveMassLocalRecalibratedEntry
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature))
        (reportRequiredSource.base_measurable.prodMk
          (reportRequiredSource.score_measurable.prodMk
            reportRequiredSource.skill_measurable))
        (fun latentSkill publicBase =>
          reportRequired.takeDecision latentSkill publicBase) →
    ∃ (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
        (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
        (baseVariance baseMeanVariance : ℝ)
        (hbaseLaw : IsProbabilityMeasure baseLaw)
        (hbaseMean : Measurable baseMean)
        (hbaseVariance : 0 < baseVariance),
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
          baseLaw ⊗ₘ gaussianLocationKernel
            baseMean hbaseMean baseVariance.toNNReal ∧
        0 ≤ baseMeanVariance ∧
        ((∀ᵐ publicBase ∂baseLaw,
           condDistrib
               (lg21ObservedAccessActualOutput
                 (lg21ContinuousPopulationBase testFeature)
                 (lg21ContinuousPopulationFeature testFeature)
                 mandatory.action mandatoryReportedPayoff mandatoryNoReportPayoff)
               (lg21ContinuousPopulationBase testFeature)
               (lg21ContinuousGaussianAccessPopulationLaw M) publicBase ≠
             condDistrib noAccessOutput
               (lg21ContinuousPopulationBase testFeature)
               (lg21ContinuousGaussianNoAccessPopulationLaw M) publicBase) ∧
          ((lg21ContinuousGaussianAccessPopulationLaw M).map
              (lg21ObservedAccessActualOutput
                (lg21ContinuousPopulationBase testFeature)
                (lg21ContinuousPopulationFeature testFeature)
                mandatory.action mandatoryReportedPayoff mandatoryNoReportPayoff) ≠
            (lg21ContinuousGaussianNoAccessPopulationLaw M).map noAccessOutput) ∧
          (∀ᵐ publicBase ∂baseLaw,
           condDistrib
               (lg21OptionalSourceTimedActualOutput
                 (lg21ContinuousPopulationBase testFeature)
                 (lg21ContinuousPopulationFeature testFeature)
                 (lg21ContinuousPopulationSkill (Feature := Feature)) optional.actions)
               (lg21ContinuousPopulationBase testFeature)
               (lg21ContinuousGaussianAccessPopulationLaw M) publicBase ≠
             condDistrib noAccessOutput
               (lg21ContinuousPopulationBase testFeature)
               (lg21ContinuousGaussianNoAccessPopulationLaw M) publicBase) ∧
          ((lg21ContinuousGaussianAccessPopulationLaw M).map
              (lg21OptionalSourceTimedActualOutput
                (lg21ContinuousPopulationBase testFeature)
                (lg21ContinuousPopulationFeature testFeature)
                (lg21ContinuousPopulationSkill (Feature := Feature)) optional.actions) ≠
            (lg21ContinuousGaussianNoAccessPopulationLaw M).map noAccessOutput) ∧
          (∀ᵐ publicBase ∂baseLaw,
           condDistrib
               (lg21ReportRequiredSequentialActualOutput
                 (lg21ContinuousPopulationBase testFeature)
                 (lg21ContinuousPopulationFeature testFeature)
                 (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired)
               (lg21ContinuousPopulationBase testFeature)
               (lg21ContinuousGaussianAccessPopulationLaw M) publicBase ≠
             condDistrib noAccessOutput
               (lg21ContinuousPopulationBase testFeature)
               (lg21ContinuousGaussianNoAccessPopulationLaw M) publicBase) ∧
          ((lg21ContinuousGaussianAccessPopulationLaw M).map
              (lg21ReportRequiredSequentialActualOutput
                (lg21ContinuousPopulationBase testFeature)
                (lg21ContinuousPopulationFeature testFeature)
                (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired) ≠
            (lg21ContinuousGaussianNoAccessPopulationLaw M).map noAccessOutput)) := by
  exact
    lg21ContinuousGaussianPopulation_allObservedAccessProtocols_actualPBO_not_observableOrDemographicFair
      M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance mandatory mandatoryReportedPayoff mandatoryNoReportPayoff
      hmandatoryReportedPBO optional reportRequired hreportRequiredTestLaw noAccessOutput
      hnoAccessPBO

/--
Conditional Section 4 Gaussian fairness gaps for all three protocol carriers.
This is analytic support, not Proposition 4.3's source-facing policy result:
the voluntary carriers are not shown nonempty and their old stability fields
do not exclude positive-mass withdrawals. In particular, this theorem must
not be used as evidence for the source definition's `not (fair in every
equilibrium)` conclusion.
-/
theorem proposition4_3_conditional_all_observed_access_protocols_fairness_gaps
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (noAccessOutput : Bool × (ℝ × (Feature -> ℝ)) -> ℝ)
    (hnoAccessPBO : LG21ContinuousGaussianNoAccessPopulationPBO
      M hnoAccess testFeature noAccessOutput) :
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    letI : IsFiniteMeasure
        (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianNoAccessPopulationLaw M) :=
      lg21ContinuousGaussianNoAccessPopulationLaw_isProbability M hnoAccess
    letI : IsFiniteMeasure
        (lg21ContinuousGaussianNoAccessPopulationLaw M) := ⟨by simp⟩
    ∃ (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
        (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
        (baseVariance baseMeanVariance : ℝ)
        (hbaseLaw : IsProbabilityMeasure baseLaw)
        (hbaseMean : Measurable baseMean)
        (hbaseVariance : 0 < baseVariance),
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
          baseLaw ⊗ₘ gaussianLocationKernel
            baseMean hbaseMean baseVariance.toNNReal ∧
        0 ≤ baseMeanVariance ∧
        baseLaw.map baseMean =
          gaussianReal M.priorMean baseMeanVariance.toNNReal ∧
        (letI : IsProbabilityMeasure baseLaw := hbaseLaw
         (∀ (mandatory : LG21MandatoryGivenAccessLiteralSourceEquilibrium M)
             (mandatoryReportedPayoff :
               (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> ℝ)
             (mandatoryNoReportPayoff :
               (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
             (hmandatoryReportedPBO : LG21ObservedAccessAllReportPBO
               (lg21ContinuousGaussianAccessPopulationLaw M)
               (lg21ContinuousPopulationBase testFeature)
               (lg21ContinuousPopulationFeature testFeature)
               (lg21ContinuousPopulationSkill (Feature := Feature))
               mandatoryReportedPayoff),
           (¬ LG21ObservedAccessDeterministicObservableFairAE baseLaw
             (lg21ContinuousPopulationBase testFeature)
             (lg21ContinuousGaussianAccessPopulationLaw M)
             (lg21ContinuousGaussianNoAccessPopulationLaw M)
             (lg21ObservedAccessDeterministicTwoBranchOutput
               lg21ContinuousPopulationAccess
               (lg21ObservedAccessActualOutput
                 (lg21ContinuousPopulationBase testFeature)
                 (lg21ContinuousPopulationFeature testFeature)
                 mandatory.action mandatoryReportedPayoff mandatoryNoReportPayoff)
               noAccessOutput)) ∧
           (¬ LG21ObservedAccessDeterministicDemographicallyFair
             (lg21ContinuousGaussianAccessPopulationLaw M)
             (lg21ContinuousGaussianNoAccessPopulationLaw M)
             (lg21ObservedAccessDeterministicTwoBranchOutput
               lg21ContinuousPopulationAccess
               (lg21ObservedAccessActualOutput
                 (lg21ContinuousPopulationBase testFeature)
                 (lg21ContinuousPopulationFeature testFeature)
                 mandatory.action mandatoryReportedPayoff mandatoryNoReportPayoff)
               noAccessOutput))) ∧
         (∀ (optional : LG21ObservedAccessOptionalSourceTimedEquilibrium
             M haccess testFeature),
           (¬ LG21ObservedAccessDeterministicObservableFairAE baseLaw
             (lg21ContinuousPopulationBase testFeature)
             (lg21ContinuousGaussianAccessPopulationLaw M)
             (lg21ContinuousGaussianNoAccessPopulationLaw M)
             (lg21ObservedAccessDeterministicTwoBranchOutput
               lg21ContinuousPopulationAccess
               (lg21OptionalSourceTimedActualOutput
                 (lg21ContinuousPopulationBase testFeature)
                 (lg21ContinuousPopulationFeature testFeature)
                 (lg21ContinuousPopulationSkill (Feature := Feature)) optional.actions)
               noAccessOutput)) ∧
           (¬ LG21ObservedAccessDeterministicDemographicallyFair
             (lg21ContinuousGaussianAccessPopulationLaw M)
             (lg21ContinuousGaussianNoAccessPopulationLaw M)
             (lg21ObservedAccessDeterministicTwoBranchOutput
               lg21ContinuousPopulationAccess
               (lg21OptionalSourceTimedActualOutput
                 (lg21ContinuousPopulationBase testFeature)
                 (lg21ContinuousPopulationFeature testFeature)
                 (lg21ContinuousPopulationSkill (Feature := Feature)) optional.actions)
               noAccessOutput))) ∧
         (∀ (reportRequired : LG21ReportRequiredSequentialEquilibriumData ℝ
             (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
             (hreportRequiredTestLaw : ∀ latentSkill publicBase,
               reportRequired.testLaw latentSkill publicBase =
                 gaussianReal latentSkill
                   ((M.noiseVariance testFeature : ℝ).toNNReal))
             (reportRequiredSource : LG21FullPublicReportRequiredSourceEquilibrium
               (lg21ContinuousGaussianAccessPopulationLaw M)
               (lg21ContinuousPopulationBase testFeature)
               (lg21ContinuousPopulationFeature testFeature)
               (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired),
           LG21ReportRequiredSourceStableAgainstPositiveMassLocalRecalibratedEntry
             (lg21ContinuousGaussianAccessPopulationLaw M)
             (lg21ContinuousPopulationBase testFeature)
             (lg21ContinuousPopulationFeature testFeature)
             (lg21ContinuousPopulationSkill (Feature := Feature))
             (reportRequiredSource.base_measurable.prodMk
               (reportRequiredSource.score_measurable.prodMk
                 reportRequiredSource.skill_measurable))
             (fun latentSkill publicBase =>
               reportRequired.takeDecision latentSkill publicBase) →
           (¬ LG21ObservedAccessDeterministicObservableFairAE baseLaw
             (lg21ContinuousPopulationBase testFeature)
             (lg21ContinuousGaussianAccessPopulationLaw M)
             (lg21ContinuousGaussianNoAccessPopulationLaw M)
             (lg21ObservedAccessDeterministicTwoBranchOutput
               lg21ContinuousPopulationAccess
               (lg21ReportRequiredSequentialActualOutput
                 (lg21ContinuousPopulationBase testFeature)
                 (lg21ContinuousPopulationFeature testFeature)
                 (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired)
               noAccessOutput)) ∧
           (¬ LG21ObservedAccessDeterministicDemographicallyFair
             (lg21ContinuousGaussianAccessPopulationLaw M)
             (lg21ContinuousGaussianNoAccessPopulationLaw M)
             (lg21ObservedAccessDeterministicTwoBranchOutput
               lg21ContinuousPopulationAccess
               (lg21ReportRequiredSequentialActualOutput
                 (lg21ContinuousPopulationBase testFeature)
                 (lg21ContinuousPopulationFeature testFeature)
                 (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired)
               noAccessOutput)))) := by
  exact
    lg21ContinuousGaussianPopulation_allObservedAccessProtocols_actualPBO_not_fair_fixedSource
      M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance noAccessOutput hnoAccessPBO

/-! ## Definition 6 and Theorem 4.4: resampling policy -/

/-- Definition 6's access-side continuous estimate kernel. -/
abbrev definition6_continuous_access_estimate_kernel :=
  @lg21ContinuousAccessEstimateKernel

/-- Definition 6's no-access continuous resampling estimate kernel. -/
abbrev definition6_continuous_resampling_estimate_kernel :=
  @lg21ContinuousResamplingEstimateKernel

/-- Definition 6's access-side estimate law. -/
abbrev definition6_continuous_access_estimate_law :=
  @paper_definition6_continuous_access_estimate_law

/-- Definition 6's no-access resampling estimate law. -/
abbrev definition6_continuous_no_access_resampling_law :=
  @paper_definition6_continuous_no_access_resampling_law

/--
Definition 6's no-access experiment, derived from the actual observed-access
Gaussian source.  It exposes the source base/score law, the synthetic
conditional Gaussian test pushforward, and the induced observable and
demographic law identities without accepting any of them as a premise.
-/
theorem definition6_observed_access_source_derived_resampling
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (hnoAccess : 0 < source.population.accessLaw {false}) :
    LG21Definition6ObservedAccessSourceWitness source hnoAccess := by
  exact lg21Definition6_observedAccess_source_witness source hnoAccess

/--
Conditional all-protocol output-law transport. Its voluntary carriers have
not been selected by the recorded active-branch convention, so it remains
analytic support rather than a source-facing Theorem 4.4 route.
-/
abbrev theorem4_4_conditional_all_observed_access_protocols_actual_output_eq_noAccessResampling :=
  @lg21ContinuousGaussianAccessPopulation_allProtocols_actualOutput_eq_noAccessResampling_of_literalSource

/-- Conditional optional actual-output resampling transport. -/
abbrev theorem4_4_conditional_optional_source_timed :=
  @lg21ContinuousGaussianPopulation_optional_sourceTimed_actualOutput_eq_noAccessResampling

/-- The mandatory source construction's Gaussian resampling equality. -/
abbrev theorem4_4_mandatory_source_gaussian_resampling_fair :=
  @LG21MandatorySection4Source.theorem44_mandatory_source_gaussian_resampling_fair

/--
Mandatory-given-access actual-output fairness under the attained PBO. This
route is nonvacuous at the action level because feasibility fixes reporting.
-/
abbrev theorem4_4_mandatory_given_access_actual_output_fairness :=
  @lg21ContinuousGaussianAccessPopulation_mandatoryObservedAccessOutput_observableAndDemographicFair_of_pbo

/--
Theorem 4.4 for reporting required given access.  The actual Gaussian source
admits an all-report PBO profile, and Definition 6's source-derived resampling
policy is observably and demographically fair for every such profile.
-/
theorem theorem4_4_mandatory_given_access_resampling_policy_fair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (hnoAccess : 0 < source.population.accessLaw {false}) :
    Nonempty (LG21P42MandatoryGivenAccessPBOProfile source) ∧
      ∀ (profile : LG21P42MandatoryGivenAccessPBOProfile source)
        (noReportPayoff :
          (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ),
        LG21T44MandatoryGivenAccessResamplingFairnessCertificate source hnoAccess
          profile noReportPayoff := by
  exact lg21T44_mandatoryGivenAccess_resampling_nonempty_and_fair source hnoAccess

/--
Optional-reporting Theorem 4.4 route under the declared active-branch
selection. The conclusion is the conditional and marginal actual-output-law
fairness result for Definition 6's resampling kernel.
-/
theorem theorem4_4_optional_active_branch_selection
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (profile : LG21OptionalActiveBranchProfile source)
    (hnoAccess : 0 < source.population.accessLaw {false}) :
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianAccessPopulationLaw source.population) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability source.population
        source.access_positive
    letI : IsFiniteMeasure
        (lg21ContinuousGaussianAccessPopulationLaw source.population) := ⟨by simp⟩
    ∃ (baseLaw : Measure (LG21NonTestFeature Feature source.test_feature -> ℝ))
        (baseMean : (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ)
        (baseVariance : ℝ) (hbaseMean : Measurable baseMean)
        (hbaseLaw : IsProbabilityMeasure baseLaw)
        (hbaseVariance : 0 < baseVariance),
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw source.population
          source.test_feature =
        baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal ∧
      (letI : IsProbabilityMeasure baseLaw := hbaseLaw
       let S : LG21GaussianPBOResamplingSource
          (LG21NonTestFeature Feature source.test_feature -> ℝ) :=
        { baseLaw := baseLaw
          baseLaw_isProbability := inferInstance
          posteriorBaseMean := baseMean
          posteriorBaseMean_measurable := hbaseMean
          posteriorBaseVariance := baseVariance.toNNReal
          posteriorBaseVariance_pos := by
            rw [NNReal.coe_pos, Real.toNNReal_pos]
            exact hbaseVariance
          testNoiseVariance := source.population.noiseVariance source.test_feature
          testNoiseVariance_pos := source.test_noise_variance_positive }
       LG21ObservedAccessFair source.population source.test_feature
         { accessOutput :=
             lg21OptionalSourceTimedActualOutput
               (lg21ContinuousPopulationBase source.test_feature)
               (lg21ContinuousPopulationFeature source.test_feature)
               (lg21ContinuousPopulationSkill (Feature := Feature))
               profile.selected.actions
           noAccessKernel := lg21D6NoAccessResamplingEstimateKernel S
           noAccessKernel_isMarkov := inferInstance }) := by
  simpa [LG21ObservedAccessFair] using
    (lg21ContinuousGaussianPopulation_optional_activeBranchSelection_resampling_observableAndDemographicFair
      source.population source.access_positive hnoAccess source.test_feature
      source.prior_variance_positive source.non_test_noise_variance_positive
      source.test_noise_variance_positive profile.selected
      profile.active_branch_selection)

/--
Report-required Theorem 4.4 route under the declared active-branch selection
and its coupled positive-branch source-PBO record. The result retains its
almost-everywhere conditional-kernel scope and does not totalize a null branch.
-/
theorem theorem4_4_report_required_active_branch_selection
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (profile : LG21ReportRequiredActiveBranchProfile source)
    (hnoAccess : 0 < source.population.accessLaw {false}) :
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianAccessPopulationLaw source.population) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability source.population
        source.access_positive
    letI : IsFiniteMeasure
        (lg21ContinuousGaussianAccessPopulationLaw source.population) := ⟨by simp⟩
    ∃ (baseLaw : Measure (LG21NonTestFeature Feature source.test_feature -> ℝ))
        (baseMean : (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ)
        (baseVariance : ℝ) (hbaseMean : Measurable baseMean)
        (hbaseLaw : IsProbabilityMeasure baseLaw)
        (hbaseVariance : 0 < baseVariance),
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw source.population
          source.test_feature =
        baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal ∧
      (letI : IsProbabilityMeasure baseLaw := hbaseLaw
       let S : LG21GaussianPBOResamplingSource
          (LG21NonTestFeature Feature source.test_feature -> ℝ) :=
        { baseLaw := baseLaw
          baseLaw_isProbability := inferInstance
          posteriorBaseMean := baseMean
          posteriorBaseMean_measurable := hbaseMean
          posteriorBaseVariance := baseVariance.toNNReal
          posteriorBaseVariance_pos := by
            rw [NNReal.coe_pos, Real.toNNReal_pos]
            exact hbaseVariance
          testNoiseVariance := source.population.noiseVariance source.test_feature
          testNoiseVariance_pos := source.test_noise_variance_positive }
       LG21ObservedAccessFair source.population source.test_feature
         { accessOutput :=
             lg21ReportRequiredSequentialActualOutput
               (lg21ContinuousPopulationBase source.test_feature)
               (lg21ContinuousPopulationFeature source.test_feature)
               (lg21ContinuousPopulationSkill (Feature := Feature)) profile.selected
           noAccessKernel := lg21D6NoAccessResamplingEstimateKernel S
           noAccessKernel_isMarkov := inferInstance }) := by
  simpa [LG21ObservedAccessFair] using
    (lg21ContinuousGaussianPopulation_reportRequired_activeBranchSelection_resampling_observableAndDemographicFair
      source.population source.access_positive hnoAccess source.test_feature
      source.prior_variance_positive source.non_test_noise_variance_positive
      source.test_noise_variance_positive profile.selected
      profile.positive_branch_pbo profile.active_branch_selection)

/--
Theorem 4.4 under the declared voluntary active-branch convention. For every
selected optional or report-required profile, the actual selected access output
and the source-derived Definition 6 no-access resampling kernel form an
`LG21ObservedAccessFair` two-branch policy. The policy comparison is
almost-everywhere on conditional fibres and does not assign a PBO or payoff to
a null voluntary action branch.
-/
theorem theorem4_4_observed_access_resampling_policy_fair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (hnoAccess : 0 < source.population.accessLaw {false}) :
    let claim : (Bool × (ℝ × (Feature -> ℝ)) -> ℝ) -> Prop :=
      fun actualOutput =>
        letI : IsProbabilityMeasure
            (lg21ContinuousGaussianAccessPopulationLaw source.population) :=
          lg21ContinuousGaussianAccessPopulationLaw_isProbability source.population
            source.access_positive
        letI : IsFiniteMeasure
            (lg21ContinuousGaussianAccessPopulationLaw source.population) := ⟨by simp⟩
        ∃ (baseLaw : Measure (LG21NonTestFeature Feature source.test_feature -> ℝ))
            (baseMean : (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ)
            (baseVariance : ℝ) (hbaseMean : Measurable baseMean)
            (hbaseLaw : IsProbabilityMeasure baseLaw)
            (hbaseVariance : 0 < baseVariance),
          lg21ContinuousGaussianFullBaseLatentPrimitiveLaw source.population
              source.test_feature =
            baseLaw ⊗ₘ gaussianLocationKernel
              baseMean hbaseMean baseVariance.toNNReal ∧
          (letI : IsProbabilityMeasure baseLaw := hbaseLaw
           let S : LG21GaussianPBOResamplingSource
              (LG21NonTestFeature Feature source.test_feature -> ℝ) :=
            { baseLaw := baseLaw
              baseLaw_isProbability := inferInstance
              posteriorBaseMean := baseMean
              posteriorBaseMean_measurable := hbaseMean
              posteriorBaseVariance := baseVariance.toNNReal
              posteriorBaseVariance_pos := by
                rw [NNReal.coe_pos, Real.toNNReal_pos]
                exact hbaseVariance
              testNoiseVariance := source.population.noiseVariance source.test_feature
              testNoiseVariance_pos := source.test_noise_variance_positive }
           LG21ObservedAccessFair source.population source.test_feature
             { accessOutput := actualOutput
               noAccessKernel := lg21D6NoAccessResamplingEstimateKernel S
               noAccessKernel_isMarkov := inferInstance })
    Nonempty (LG21OptionalActiveBranchProfile source) ∧
      Nonempty (LG21ReportRequiredActiveBranchProfile source) ∧
      (∀ optionalProfile : LG21OptionalActiveBranchProfile source,
        claim
          (lg21OptionalSourceTimedActualOutput
            (lg21ContinuousPopulationBase source.test_feature)
            (lg21ContinuousPopulationFeature source.test_feature)
            (lg21ContinuousPopulationSkill (Feature := Feature))
            optionalProfile.selected.actions)) ∧
      ∀ reportRequiredProfile : LG21ReportRequiredActiveBranchProfile source,
        claim
          (lg21ReportRequiredSequentialActualOutput
            (lg21ContinuousPopulationBase source.test_feature)
            (lg21ContinuousPopulationFeature source.test_feature)
            (lg21ContinuousPopulationSkill (Feature := Feature))
            reportRequiredProfile.selected) := by
  dsimp
  exact ⟨
    lg21ObservedAccessGaussianSource_optionalActiveBranchProfile_nonempty source,
    lg21ObservedAccessGaussianSource_reportRequiredActiveBranchProfile_nonempty source,
    fun optionalProfile =>
      theorem4_4_optional_active_branch_selection source optionalProfile hnoAccess,
    fun reportRequiredProfile =>
      theorem4_4_report_required_active_branch_selection source
        reportRequiredProfile hnoAccess⟩

/--
Theorem 4.4 across the three requirement policies advertised by the source.
Each conjunct is a separate protocol instance of Definition 6's common
source-derived resampling construction. The statement does not invent a
simultaneous profile, require a common off-path voluntary action, or use the
conditional legacy all-protocol bridge as source-result evidence.
-/
def theorem4_4_all_observed_access_requirement_protocolsSpec : Prop :=
  ∀ {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (hnoAccess : 0 < source.population.accessLaw {false}),
    (let claim : (Bool × (ℝ × (Feature -> ℝ)) -> ℝ) -> Prop :=
      fun actualOutput =>
        letI : IsProbabilityMeasure
            (lg21ContinuousGaussianAccessPopulationLaw source.population) :=
          lg21ContinuousGaussianAccessPopulationLaw_isProbability source.population
            source.access_positive
        letI : IsFiniteMeasure
            (lg21ContinuousGaussianAccessPopulationLaw source.population) := ⟨by simp⟩
        ∃ (baseLaw : Measure (LG21NonTestFeature Feature source.test_feature -> ℝ))
            (baseMean : (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ)
            (baseVariance : ℝ) (hbaseMean : Measurable baseMean)
            (hbaseLaw : IsProbabilityMeasure baseLaw)
            (hbaseVariance : 0 < baseVariance),
          lg21ContinuousGaussianFullBaseLatentPrimitiveLaw source.population
              source.test_feature =
            baseLaw ⊗ₘ gaussianLocationKernel
              baseMean hbaseMean baseVariance.toNNReal ∧
          (letI : IsProbabilityMeasure baseLaw := hbaseLaw
           let S : LG21GaussianPBOResamplingSource
              (LG21NonTestFeature Feature source.test_feature -> ℝ) :=
            { baseLaw := baseLaw
              baseLaw_isProbability := inferInstance
              posteriorBaseMean := baseMean
              posteriorBaseMean_measurable := hbaseMean
              posteriorBaseVariance := baseVariance.toNNReal
              posteriorBaseVariance_pos := by
                rw [NNReal.coe_pos, Real.toNNReal_pos]
                exact hbaseVariance
              testNoiseVariance := source.population.noiseVariance source.test_feature
              testNoiseVariance_pos := source.test_noise_variance_positive }
           LG21ObservedAccessFair source.population source.test_feature
             { accessOutput := actualOutput
               noAccessKernel := lg21D6NoAccessResamplingEstimateKernel S
               noAccessKernel_isMarkov := inferInstance })
     Nonempty (LG21OptionalActiveBranchProfile source) ∧
      Nonempty (LG21ReportRequiredActiveBranchProfile source) ∧
      (∀ optionalProfile : LG21OptionalActiveBranchProfile source,
        claim
          (lg21OptionalSourceTimedActualOutput
            (lg21ContinuousPopulationBase source.test_feature)
            (lg21ContinuousPopulationFeature source.test_feature)
            (lg21ContinuousPopulationSkill (Feature := Feature))
            optionalProfile.selected.actions)) ∧
      ∀ reportRequiredProfile : LG21ReportRequiredActiveBranchProfile source,
        claim
          (lg21ReportRequiredSequentialActualOutput
            (lg21ContinuousPopulationBase source.test_feature)
            (lg21ContinuousPopulationFeature source.test_feature)
            (lg21ContinuousPopulationSkill (Feature := Feature))
            reportRequiredProfile.selected)) ∧
    (Nonempty (LG21P42MandatoryGivenAccessPBOProfile source) ∧
      ∀ (profile : LG21P42MandatoryGivenAccessPBOProfile source)
        (mandatoryNoReportPayoff :
          (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ),
        LG21T44MandatoryGivenAccessResamplingFairnessCertificate source hnoAccess
          profile mandatoryNoReportPayoff)

theorem theorem4_4_all_observed_access_requirement_protocols :
    theorem4_4_all_observed_access_requirement_protocolsSpec := by
  dsimp only [theorem4_4_all_observed_access_requirement_protocolsSpec]
  intro Feature instFintype instDecidableEq source hnoAccess
  exact ⟨
    theorem4_4_observed_access_resampling_policy_fair source hnoAccess,
    theorem4_4_mandatory_given_access_resampling_policy_fair source hnoAccess⟩

/--
The paper-facing core of Theorem 4.4. It keeps the Definition 6 resampling
fairness conclusion for every profile under each requirement regime and omits
only the aggregate theorem's independent profile-existence packages.
-/
def theorem4_4_all_observed_access_requirement_protocols_source_coreSpec : Prop :=
  ∀ {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (hnoAccess : 0 < source.population.accessLaw {false}),
    (let claim : (Bool × (ℝ × (Feature -> ℝ)) -> ℝ) -> Prop :=
      fun actualOutput =>
        letI : IsProbabilityMeasure
            (lg21ContinuousGaussianAccessPopulationLaw source.population) :=
          lg21ContinuousGaussianAccessPopulationLaw_isProbability source.population
            source.access_positive
        letI : IsFiniteMeasure
            (lg21ContinuousGaussianAccessPopulationLaw source.population) := ⟨by simp⟩
        ∃ (baseLaw : Measure (LG21NonTestFeature Feature source.test_feature -> ℝ))
            (baseMean : (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ)
            (baseVariance : ℝ) (hbaseMean : Measurable baseMean)
            (hbaseLaw : IsProbabilityMeasure baseLaw)
            (hbaseVariance : 0 < baseVariance),
          lg21ContinuousGaussianFullBaseLatentPrimitiveLaw source.population
              source.test_feature =
            baseLaw ⊗ₘ gaussianLocationKernel
              baseMean hbaseMean baseVariance.toNNReal ∧
          (letI : IsProbabilityMeasure baseLaw := hbaseLaw
           let S : LG21GaussianPBOResamplingSource
              (LG21NonTestFeature Feature source.test_feature -> ℝ) :=
            { baseLaw := baseLaw
              baseLaw_isProbability := inferInstance
              posteriorBaseMean := baseMean
              posteriorBaseMean_measurable := hbaseMean
              posteriorBaseVariance := baseVariance.toNNReal
              posteriorBaseVariance_pos := by
                rw [NNReal.coe_pos, Real.toNNReal_pos]
                exact hbaseVariance
              testNoiseVariance := source.population.noiseVariance source.test_feature
              testNoiseVariance_pos := source.test_noise_variance_positive }
           LG21ObservedAccessFair source.population source.test_feature
             { accessOutput := actualOutput
               noAccessKernel := lg21D6NoAccessResamplingEstimateKernel S
               noAccessKernel_isMarkov := inferInstance })
     (∀ optionalProfile : LG21OptionalActiveBranchProfile source,
        claim
          (lg21OptionalSourceTimedActualOutput
            (lg21ContinuousPopulationBase source.test_feature)
            (lg21ContinuousPopulationFeature source.test_feature)
            (lg21ContinuousPopulationSkill (Feature := Feature))
            optionalProfile.selected.actions)) ∧
      ∀ reportRequiredProfile : LG21ReportRequiredActiveBranchProfile source,
        claim
          (lg21ReportRequiredSequentialActualOutput
            (lg21ContinuousPopulationBase source.test_feature)
            (lg21ContinuousPopulationFeature source.test_feature)
            (lg21ContinuousPopulationSkill (Feature := Feature))
            reportRequiredProfile.selected)) ∧
    ∀ (profile : LG21P42MandatoryGivenAccessPBOProfile source)
      (mandatoryNoReportPayoff :
        (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ),
      LG21T44MandatoryGivenAccessResamplingFairnessCertificate source hnoAccess
        profile mandatoryNoReportPayoff

theorem theorem4_4_all_observed_access_requirement_protocols_source_core :
    theorem4_4_all_observed_access_requirement_protocols_source_coreSpec := by
  dsimp only [theorem4_4_all_observed_access_requirement_protocols_source_coreSpec]
  intro Feature instFintype instDecidableEq source hnoAccess
  have voluntary := theorem4_4_observed_access_resampling_policy_fair source hnoAccess
  have mandatory :=
    theorem4_4_mandatory_given_access_resampling_policy_fair source hnoAccess
  exact ⟨voluntary.2.2, mandatory.2⟩

/--
Internal simultaneous aggregation of Theorem 4.4's independent protocol
routes.  It is not the paper-facing route: the source applies separately to
each requirement protocol.  The direct independent endpoints follow below.
-/
theorem theorem4_4_simultaneous_protocols_auxiliary
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (mandatory : LG21MandatoryGivenAccessLiteralSourceEquilibrium M)
    (mandatoryReportedPayoff :
      (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> ℝ)
    (mandatoryNoReportPayoff :
      (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hmandatoryReportedPBO : LG21ObservedAccessAllReportPBO
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) mandatoryReportedPayoff)
    (optional : LG21ObservedAccessOptionalSourceTimedEquilibrium
      M haccess testFeature)
    (reportRequired : LG21ReportRequiredSequentialEquilibriumData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    (hreportRequiredTestLaw : ∀ latentSkill publicBase,
      reportRequired.testLaw latentSkill publicBase = gaussianReal latentSkill
        ((M.noiseVariance testFeature : ℝ).toNNReal)) :
    letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    letI : IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
    ∀ (reportRequiredSource : LG21FullPublicReportRequiredSourceEquilibrium
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired),
      LG21ReportRequiredSourceStableAgainstPositiveMassLocalRecalibratedEntry
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature))
        (reportRequiredSource.base_measurable.prodMk
          (reportRequiredSource.score_measurable.prodMk
            reportRequiredSource.skill_measurable))
        (fun latentSkill publicBase =>
          reportRequired.takeDecision latentSkill publicBase) →
    ∃ (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
        (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
        (baseVariance : ℝ) (hbaseMean : Measurable baseMean)
        (hbaseLaw : IsProbabilityMeasure baseLaw)
        (hbaseVariance : 0 < baseVariance),
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal ∧
      (letI : IsProbabilityMeasure baseLaw := hbaseLaw
       let S : LG21GaussianPBOResamplingSource
          (LG21NonTestFeature Feature testFeature -> ℝ) :=
        { baseLaw := baseLaw
          baseLaw_isProbability := inferInstance
          posteriorBaseMean := baseMean
          posteriorBaseMean_measurable := hbaseMean
          posteriorBaseVariance := baseVariance.toNNReal
          posteriorBaseVariance_pos := by
            rw [NNReal.coe_pos, Real.toNNReal_pos]
            exact hbaseVariance
          testNoiseVariance := M.noiseVariance testFeature
          testNoiseVariance_pos := htestNoiseVariance }
       let mandatoryOutput := lg21ObservedAccessActualOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          mandatory.action mandatoryReportedPayoff mandatoryNoReportPayoff
       let optionalOutput := lg21OptionalSourceTimedActualOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) optional.actions
       let reportRequiredOutput := lg21ReportRequiredSequentialActualOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired
       (condDistrib mandatoryOutput (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousGaussianAccessPopulationLaw M) =ᵐ[
            (lg21ContinuousGaussianAccessPopulationLaw M).map
              (lg21ContinuousPopulationBase testFeature)]
            lg21D6NoAccessResamplingEstimateKernel S) ∧
        ((lg21ContinuousGaussianAccessPopulationLaw M).map mandatoryOutput =
          Measure.bind
            ((lg21ContinuousGaussianNoAccessPopulationLaw M).map
              (lg21ContinuousPopulationBase testFeature))
            (lg21D6NoAccessResamplingEstimateKernel S)) ∧
        (condDistrib optionalOutput (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousGaussianAccessPopulationLaw M) =ᵐ[
            (lg21ContinuousGaussianAccessPopulationLaw M).map
              (lg21ContinuousPopulationBase testFeature)]
            lg21D6NoAccessResamplingEstimateKernel S) ∧
        ((lg21ContinuousGaussianAccessPopulationLaw M).map optionalOutput =
          Measure.bind
            ((lg21ContinuousGaussianNoAccessPopulationLaw M).map
              (lg21ContinuousPopulationBase testFeature))
            (lg21D6NoAccessResamplingEstimateKernel S)) ∧
        (condDistrib reportRequiredOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousGaussianAccessPopulationLaw M) =ᵐ[
            (lg21ContinuousGaussianAccessPopulationLaw M).map
              (lg21ContinuousPopulationBase testFeature)]
            lg21D6NoAccessResamplingEstimateKernel S) ∧
        ((lg21ContinuousGaussianAccessPopulationLaw M).map reportRequiredOutput =
          Measure.bind
            ((lg21ContinuousGaussianNoAccessPopulationLaw M).map
              (lg21ContinuousPopulationBase testFeature))
            (lg21D6NoAccessResamplingEstimateKernel S))) := by
  exact
    lg21ContinuousGaussianPopulation_allObservedAccessProtocols_resampling_observableAndDemographicFair
      M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance mandatory mandatoryReportedPayoff mandatoryNoReportPayoff
      hmandatoryReportedPBO optional reportRequired hreportRequiredTestLaw

/--
Conditional Section 4 resampling-law equality for all three protocol carriers.
This is analytic support, not Theorem 4.4's source-facing selected-action
claim. The direct active-branch endpoints above carry the voluntary
operational convention and derive their own actual output laws.
-/
theorem theorem4_4_conditional_all_observed_access_protocols_resampling_fairness
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ)) :
    ∃ (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
        (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
        (baseVariance : ℝ) (hbaseMean : Measurable baseMean)
        (hbaseLaw : IsProbabilityMeasure baseLaw)
        (hbaseVariance : 0 < baseVariance),
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal ∧
      (letI : IsProbabilityMeasure baseLaw := hbaseLaw
       let S : LG21GaussianPBOResamplingSource
          (LG21NonTestFeature Feature testFeature -> ℝ) :=
        { baseLaw := baseLaw
          baseLaw_isProbability := inferInstance
          posteriorBaseMean := baseMean
          posteriorBaseMean_measurable := hbaseMean
          posteriorBaseVariance := baseVariance.toNNReal
          posteriorBaseVariance_pos := by
            rw [NNReal.coe_pos, Real.toNNReal_pos]
            exact hbaseVariance
          testNoiseVariance := M.noiseVariance testFeature
          testNoiseVariance_pos := htestNoiseVariance }
       letI : IsProbabilityMeasure
          (lg21ContinuousGaussianAccessPopulationLaw M) :=
          lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
       letI : IsFiniteMeasure
          (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
       (∀ (mandatory : LG21MandatoryGivenAccessLiteralSourceEquilibrium M)
           (reportedPayoff :
             (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> ℝ)
           (noReportPayoff :
             (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
           (hreportedPBO : LG21ObservedAccessAllReportPBO
             (lg21ContinuousGaussianAccessPopulationLaw M)
             (lg21ContinuousPopulationBase testFeature)
             (lg21ContinuousPopulationFeature testFeature)
             (lg21ContinuousPopulationSkill (Feature := Feature)) reportedPayoff),
         LG21ObservedAccessFair M testFeature
          { accessOutput := lg21ObservedAccessActualOutput
              (lg21ContinuousPopulationBase testFeature)
              (lg21ContinuousPopulationFeature testFeature)
              mandatory.action reportedPayoff noReportPayoff
            noAccessKernel := lg21D6NoAccessResamplingEstimateKernel S
            noAccessKernel_isMarkov := inferInstance }) ∧
       (∀ (optional : LG21ObservedAccessOptionalSourceTimedEquilibrium
           M haccess testFeature),
         LG21ObservedAccessFair M testFeature
          { accessOutput := lg21OptionalSourceTimedActualOutput
              (lg21ContinuousPopulationBase testFeature)
              (lg21ContinuousPopulationFeature testFeature)
              (lg21ContinuousPopulationSkill (Feature := Feature)) optional.actions
            noAccessKernel := lg21D6NoAccessResamplingEstimateKernel S
            noAccessKernel_isMarkov := inferInstance }) ∧
       (∀ (reportRequired : LG21ReportRequiredSequentialEquilibriumData ℝ
           (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
           (htestLaw : ∀ latentSkill publicBase,
             reportRequired.testLaw latentSkill publicBase = gaussianReal latentSkill
               ((M.noiseVariance testFeature : ℝ).toNNReal))
           (source : LG21FullPublicReportRequiredSourceEquilibrium
             (lg21ContinuousGaussianAccessPopulationLaw M)
             (lg21ContinuousPopulationBase testFeature)
             (lg21ContinuousPopulationFeature testFeature)
             (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired),
         LG21ReportRequiredSourceStableAgainstPositiveMassLocalRecalibratedEntry
           (lg21ContinuousGaussianAccessPopulationLaw M)
           (lg21ContinuousPopulationBase testFeature)
           (lg21ContinuousPopulationFeature testFeature)
           (lg21ContinuousPopulationSkill (Feature := Feature))
           (source.base_measurable.prodMk
             (source.score_measurable.prodMk source.skill_measurable))
           (fun latentSkill publicBase =>
             reportRequired.takeDecision latentSkill publicBase) →
         LG21ObservedAccessFair M testFeature
          { accessOutput := lg21ReportRequiredSequentialActualOutput
              (lg21ContinuousPopulationBase testFeature)
              (lg21ContinuousPopulationFeature testFeature)
              (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired
            noAccessKernel := lg21D6NoAccessResamplingEstimateKernel S
            noAccessKernel_isMarkov := inferInstance })) := by
  exact
    lg21ContinuousGaussianPopulation_allObservedAccessProtocols_resampling_observedAccessFair_fixedPolicy
      M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance

end PaperInterface

end

end LG21TestOptionalPolicies
