import LG21TestOptionalPolicies.Theorem32ReportRequiredGaussianConclusion

/-!
# Clarified operational model for LG21 Theorem 3.2

This module is the governing Lean model for the repaired Theorem 3.2 route.
It keeps optional reporting and report-required-after-taking as independent
requirement-policy schedules.  Each schedule is indexed by both a supplied
equilibrium and a fixed non-test-feature fibre.

The clarified policy condition is narrow: the whole information branch in
which a score is reported has a deterministic estimate.  The no-report branch
remains an arbitrary common probability law.  The conclusion is operational:
it concerns the output law actually induced in equilibrium, rather than raw
policy values at score inputs that have zero equilibrium probability.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory

universe u

/--
The optional-reporting source schedule.  The fields marked technical package
measurability, probability, and integration facts needed to state Definition
1's expected-payoff condition over a continuous population; they are not
additional economic restrictions.
-/
structure LG21ClarifiedOptionalReportingModel
    (Base : Type u) [MeasurableSpace Base] where
  /-- Definitions 2--5's law surface for the optional-reporting protocol. -/
  policy : LG21SourceLawPolicySurface.{0, u, 0, 0, u} ℝ Base ℝ (Measure ℝ)
  /-- Source Definition 2 implies Definition 3 for this supplied law model. -/
  latentSkillFair_implies_observablyFair :
    lg21SourceLawLatentSkillFair policy ->
      lg21SourceLawObservablyFair policy

  /- Source score law and equilibrium reporting strategy; measurability is technical. -/
  scoreLaw : policy.Equilibrium -> Base -> Measure ℝ
  scoreLaw_probability : ∀ e base, IsProbabilityMeasure (scoreLaw e base)
  reporterSet : policy.Equilibrium -> Base -> Set ℝ
  reporterSet_measurable : ∀ e base, MeasurableSet (reporterSet e base)

  /--
  Clarified policy condition: the entire reported-score information branch,
  including counterfactual scores, has a deterministic output value.
  -/
  reporterOutput : policy.Equilibrium -> Base -> ℝ -> ℝ
  reporterOutput_measurable : ∀ e base, Measurable (reporterOutput e base)
  fullFeatureLaw_is_dirac :
    ∀ e base score,
      policy.fullFeatureLaw e base score =
        Measure.dirac (reporterOutput e base score)

  /-- The arbitrary common no-report law at this fixed equilibrium/fibre. -/
  baseOnlyLaw_probability :
    ∀ e base, IsProbabilityMeasure (policy.baseOnlyLaw e base)
  /-- Source-facing finite expected no-report estimate condition. -/
  baseOnlyLaw_integrable :
    ∀ e base, Integrable id (policy.baseOnlyLaw e base)

  /- Technical tower/integrability packaging for the operational output kernel. -/
  operationalMean_integrable :
    ∀ e base,
      Integrable
        (fun score =>
          ∫ estimate,
            estimate ∂lg21OptionalDeterministicReporterKernel
              (reporterSet e base)
              (reporterSet_measurable e base)
              (reporterOutput e base)
              (reporterOutput_measurable e base)
              (policy.baseOnlyLaw e base) score)
        (scoreLaw e base)
  mean_tower :
    ∀ e base,
      (∫ score,
          ∫ estimate,
            estimate ∂lg21OptionalDeterministicReporterKernel
              (reporterSet e base)
              (reporterSet_measurable e base)
              (reporterOutput e base)
              (reporterOutput_measurable e base)
              (policy.baseOnlyLaw e base) score
          ∂scoreLaw e base) =
        ∫ estimate,
          estimate ∂(scoreLaw e base).bind
            (lg21OptionalDeterministicReporterKernel
              (reporterSet e base)
              (reporterSet_measurable e base)
              (reporterOutput e base)
              (reporterOutput_measurable e base)
              (policy.baseOnlyLaw e base))

  /--
  The clarified operational model's explicit no-profitable-withholding
  consequence on actual reporters.  It is intended to represent the relevant
  Definition 1 consequence, but is not derived here from bare Definition 1.
  -/
  reporter_bestResponse :
    ∀ e base,
      ∀ᵐ score ∂(scoreLaw e base).restrict (reporterSet e base),
        (∫ estimate, estimate ∂policy.baseOnlyLaw e base) <=
          reporterOutput e base score
  /- Source-law links: Definition 3 equates these two law-valued surfaces. -/
  operationalLaw_eq_observableAccess :
    ∀ e base,
      (scoreLaw e base).bind
        (lg21OptionalDeterministicReporterKernel
          (reporterSet e base)
          (reporterSet_measurable e base)
          (reporterOutput e base)
          (reporterOutput_measurable e base)
          (policy.baseOnlyLaw e base)) =
        policy.observableAccessLaw e base
  noAccessLaw_eq_baseOnly :
    ∀ e base,
      policy.observableNoAccessLaw e base = policy.baseOnlyLaw e base

/--
The report-required-after-taking source schedule.  The all-shifts L1 field is
the explicit finite-expected-reporter-output clarification of Definition 1:
every latent skill type evaluates a Gaussian score draw.  It is stronger than
the source's informal word "expectation", so it remains visible here and in
the post-formalization report.
-/
structure LG21ClarifiedReportRequiredModel
    (Base : Type u) [MeasurableSpace Base] where
  /-- Definitions 2--5's law surface for the report-required protocol. -/
  policy : LG21SourceLawPolicySurface.{0, u, 0, 0, u} ℝ Base ℝ (Measure ℝ)
  /-- Source Definition 2 implies Definition 3 for this supplied law model. -/
  latentSkillFair_implies_observablyFair :
    lg21SourceLawLatentSkillFair policy ->
      lg21SourceLawObservablyFair policy

  /- Gaussian source-model regularity.  Nonzero variances express the paper's noisy Gaussian setting. -/
  populationMean : policy.Equilibrium -> Base -> ℝ
  populationVariance : policy.Equilibrium -> Base -> NNReal
  populationVariance_ne_zero : ∀ e base, populationVariance e base ≠ 0
  noiseVariance : policy.Equilibrium -> Base -> NNReal
  noiseVariance_ne_zero : ∀ e base, noiseVariance e base ≠ 0

  /- Source strategy and technical measurability representation. -/
  takerSet : policy.Equilibrium -> Base -> Set ℝ
  takerSet_measurable : ∀ e base, MeasurableSet (takerSet e base)
  /-- Clarified deterministic output on the entire reported-score branch. -/
  reporterOutput : policy.Equilibrium -> Base -> ℝ -> ℝ
  reporterOutput_measurable : ∀ e base, Measurable (reporterOutput e base)
  reporterOutput_integrable_all_gaussian_shifts :
    ∀ e base mean,
      Integrable (reporterOutput e base)
        (gaussianReal mean (noiseVariance e base))
  fullFeatureLaw_is_dirac :
    ∀ e base score,
      policy.fullFeatureLaw e base score =
        Measure.dirac (reporterOutput e base score)

  /-- The arbitrary common no-take law at this fixed equilibrium/fibre. -/
  baseOnlyLaw_probability :
    ∀ e base, IsProbabilityMeasure (policy.baseOnlyLaw e base)
  /-- Source-facing finite expected no-take estimate condition. -/
  baseOnlyLaw_integrable :
    ∀ e base, Integrable id (policy.baseOnlyLaw e base)

  /- The reported score-to-output kernel and technical tower representation. -/
  reportedKernel : policy.Equilibrium -> Base -> Kernel ℝ ℝ
  reportedKernel_eq_gaussian_map :
    ∀ e base skill,
      reportedKernel e base skill =
        (gaussianReal skill (noiseVariance e base)).map (reporterOutput e base)
  operationalMean_integrable :
    ∀ e base,
      Integrable
        (fun skill =>
          ∫ estimate,
            estimate ∂lg21ReportRequiredOperationalKernel
              (takerSet e base)
              (takerSet_measurable e base)
              (reportedKernel e base)
              (policy.baseOnlyLaw e base) skill)
        (gaussianReal (populationMean e base) (populationVariance e base))
  mean_tower :
    ∀ e base,
      (∫ skill,
          ∫ estimate,
            estimate ∂lg21ReportRequiredOperationalKernel
              (takerSet e base)
              (takerSet_measurable e base)
              (reportedKernel e base)
              (policy.baseOnlyLaw e base) skill
          ∂gaussianReal (populationMean e base) (populationVariance e base)) =
        ∫ estimate,
          estimate ∂(gaussianReal (populationMean e base)
            (populationVariance e base)).bind
              (lg21ReportRequiredOperationalKernel
                (takerSet e base)
                (takerSet_measurable e base)
                (reportedKernel e base)
                (policy.baseOnlyLaw e base))

  /--
  The clarified operational model's explicit no-profitable-nontaking
  consequence on actual takers.  It is intended to represent the relevant
  Definition 1 consequence, but is not derived here from bare Definition 1.
  -/
  taker_bestResponse :
    ∀ e base,
      ∀ᵐ skill ∂(gaussianReal (populationMean e base)
        (populationVariance e base)).restrict (takerSet e base),
        (∫ estimate, estimate ∂policy.baseOnlyLaw e base) <=
          GaussianConvolutionRigidity.gaussianConvolution
            (reporterOutput e base) (noiseVariance e base) skill
  /- Source-law links: Definition 3 equates these two law-valued surfaces. -/
  operationalLaw_eq_observableAccess :
    ∀ e base,
      (gaussianReal (populationMean e base) (populationVariance e base)).bind
          (lg21ReportRequiredOperationalKernel
            (takerSet e base)
            (takerSet_measurable e base)
            (reportedKernel e base)
            (policy.baseOnlyLaw e base)) =
        policy.observableAccessLaw e base
  noAccessLaw_eq_baseOnly :
    ∀ e base,
      policy.observableNoAccessLaw e base = policy.baseOnlyLaw e base

/-- The two independent requirement-policy schedules covered by Theorem 3.2. -/
structure LG21ClarifiedTheorem32Model
    (Base : Type u) [MeasurableSpace Base] where
  optional : LG21ClarifiedOptionalReportingModel Base
  reportRequired : LG21ClarifiedReportRequiredModel Base

namespace LG21ClarifiedOptionalReportingModel

/-- The source's latent-or-observable fairness disjunction yields observable fairness. -/
theorem observablyFair_of_latent_or_observable
    {Base : Type u} [MeasurableSpace Base]
    (model : LG21ClarifiedOptionalReportingModel Base)
    (hFair : lg21SourceLawLatentSkillFair model.policy \/
      lg21SourceLawObservablyFair model.policy) :
    lg21SourceLawObservablyFair model.policy :=
  hFair.elim model.latentSkillFair_implies_observablyFair id

/-- The clarified optional-reporting Theorem 3.2, for every supplied fibre. -/
theorem operationalTestBlank_of_latent_or_observable
    {Base : Type u} [MeasurableSpace Base]
    (model : LG21ClarifiedOptionalReportingModel Base)
    (hFair : lg21SourceLawLatentSkillFair model.policy \/
      lg21SourceLawObservablyFair model.policy)
    (e : model.policy.Equilibrium) (base : Base) :
    LG21OptionalOperationalTestBlank
      (model.scoreLaw e base)
      (model.policy.baseOnlyLaw e base)
      (model.reporterSet e base)
      (lg21OptionalDeterministicReporterKernel
        (model.reporterSet e base)
        (model.reporterSet_measurable e base)
        (model.reporterOutput e base)
        (model.reporterOutput_measurable e base)
        (model.policy.baseOnlyLaw e base)) := by
  letI : IsProbabilityMeasure (model.scoreLaw e base) :=
    model.scoreLaw_probability e base
  letI : IsProbabilityMeasure (model.policy.baseOnlyLaw e base) :=
    model.baseOnlyLaw_probability e base
  have hObservable := model.observablyFair_of_latent_or_observable hFair
  have hOperationalFairness :
      (model.scoreLaw e base).bind
        (lg21OptionalDeterministicReporterKernel
          (model.reporterSet e base)
          (model.reporterSet_measurable e base)
          (model.reporterOutput e base)
          (model.reporterOutput_measurable e base)
          (model.policy.baseOnlyLaw e base)) =
        model.policy.baseOnlyLaw e base := by
    calc
      (model.scoreLaw e base).bind
          (lg21OptionalDeterministicReporterKernel
            (model.reporterSet e base)
            (model.reporterSet_measurable e base)
            (model.reporterOutput e base)
            (model.reporterOutput_measurable e base)
            (model.policy.baseOnlyLaw e base)) =
          model.policy.observableAccessLaw e base :=
        model.operationalLaw_eq_observableAccess e base
      _ = model.policy.observableNoAccessLaw e base := hObservable e base
      _ = model.policy.baseOnlyLaw e base := model.noAccessLaw_eq_baseOnly e base
  exact lg21_optional_reporting_operational_test_blank_of_deterministic_reporters
    (model.scoreLaw e base) (model.policy.baseOnlyLaw e base)
    (model.reporterSet e base) (model.reporterSet_measurable e base)
    (model.reporterOutput e base) (model.reporterOutput_measurable e base)
    (model.baseOnlyLaw_integrable e base)
    (model.operationalMean_integrable e base)
    (model.mean_tower e base) hOperationalFairness
    (model.reporter_bestResponse e base)

end LG21ClarifiedOptionalReportingModel

namespace LG21ClarifiedReportRequiredModel

/-- The source's latent-or-observable fairness disjunction yields observable fairness. -/
theorem observablyFair_of_latent_or_observable
    {Base : Type u} [MeasurableSpace Base]
    (model : LG21ClarifiedReportRequiredModel Base)
    (hFair : lg21SourceLawLatentSkillFair model.policy \/
      lg21SourceLawObservablyFair model.policy) :
    lg21SourceLawObservablyFair model.policy :=
  hFair.elim model.latentSkillFair_implies_observablyFair id

/--
Operational blankness for report-required-after-taking at one equilibrium and
fibre.  The zero-taker case is the source's equilibrium blankness convention;
the positive branch is actual-kernel equality almost everywhere.
-/
def operationalTestBlank
    {Base : Type u} [MeasurableSpace Base]
    (model : LG21ClarifiedReportRequiredModel Base)
    (e : model.policy.Equilibrium) (base : Base) : Prop :=
  gaussianReal (model.populationMean e base) (model.populationVariance e base)
      (model.takerSet e base) = 0 \/
    ∀ᵐ skill ∂gaussianReal (model.populationMean e base)
      (model.populationVariance e base),
      lg21ReportRequiredOperationalKernel
        (model.takerSet e base)
        (model.takerSet_measurable e base)
        (model.reportedKernel e base)
        (model.policy.baseOnlyLaw e base) skill = model.policy.baseOnlyLaw e base

/-- The clarified report-required Theorem 3.2, for every supplied fibre. -/
theorem operationalTestBlank_of_latent_or_observable
    {Base : Type u} [MeasurableSpace Base]
    (model : LG21ClarifiedReportRequiredModel Base)
    (hFair : lg21SourceLawLatentSkillFair model.policy \/
      lg21SourceLawObservablyFair model.policy)
    (e : model.policy.Equilibrium) (base : Base) :
    model.operationalTestBlank e base := by
  letI : IsProbabilityMeasure (model.policy.baseOnlyLaw e base) :=
    model.baseOnlyLaw_probability e base
  have hObservable := model.observablyFair_of_latent_or_observable hFair
  have hOperationalFairness :
      (gaussianReal (model.populationMean e base)
        (model.populationVariance e base)).bind
          (lg21ReportRequiredOperationalKernel
            (model.takerSet e base)
            (model.takerSet_measurable e base)
            (model.reportedKernel e base)
            (model.policy.baseOnlyLaw e base)) =
        model.policy.baseOnlyLaw e base := by
    calc
      (gaussianReal (model.populationMean e base)
        (model.populationVariance e base)).bind
          (lg21ReportRequiredOperationalKernel
            (model.takerSet e base)
            (model.takerSet_measurable e base)
            (model.reportedKernel e base)
            (model.policy.baseOnlyLaw e base)) =
          model.policy.observableAccessLaw e base :=
        model.operationalLaw_eq_observableAccess e base
      _ = model.policy.observableNoAccessLaw e base := hObservable e base
      _ = model.policy.baseOnlyLaw e base := model.noAccessLaw_eq_baseOnly e base
  by_cases hZeroTaking :
      gaussianReal (model.populationMean e base) (model.populationVariance e base)
        (model.takerSet e base) = 0
  · exact Or.inl hZeroTaking
  · right
    have hPositiveTaking :
        0 < gaussianReal (model.populationMean e base)
          (model.populationVariance e base) (model.takerSet e base) :=
      pos_iff_ne_zero.mpr hZeroTaking
    obtain ⟨_hBaseLaw, hOperationalBlank⟩ :=
      lg21_report_required_operational_blank_ae_of_deterministic_gaussian_reporters
        (model.policy.baseOnlyLaw e base)
        (model.populationMean e base)
        (model.populationVariance e base) (model.noiseVariance e base)
        (model.populationVariance_ne_zero e base)
        (model.noiseVariance_ne_zero e base)
        (model.takerSet e base) (model.takerSet_measurable e base)
        (model.reportedKernel e base) (model.reporterOutput e base)
        (model.reportedKernel_eq_gaussian_map e base)
        (model.reporterOutput_integrable_all_gaussian_shifts e base)
        (model.operationalMean_integrable e base)
        (model.mean_tower e base) hOperationalFairness
        (model.taker_bestResponse e base) hPositiveTaking
    exact hOperationalBlank

end LG21ClarifiedReportRequiredModel

namespace LG21ClarifiedTheorem32Model

/-- The clarified operational Theorem 3.2 covers both independent schedules. -/
theorem operationalTestBlank_of_latent_or_observable
    {Base : Type u} [MeasurableSpace Base]
    (model : LG21ClarifiedTheorem32Model Base)
    (hOptionalFair :
      lg21SourceLawLatentSkillFair model.optional.policy \/
        lg21SourceLawObservablyFair model.optional.policy)
    (hReportRequiredFair :
      lg21SourceLawLatentSkillFair model.reportRequired.policy \/
        lg21SourceLawObservablyFair model.reportRequired.policy) :
    (∀ e base,
      LG21OptionalOperationalTestBlank
        (model.optional.scoreLaw e base)
        (model.optional.policy.baseOnlyLaw e base)
        (model.optional.reporterSet e base)
        (lg21OptionalDeterministicReporterKernel
          (model.optional.reporterSet e base)
          (model.optional.reporterSet_measurable e base)
          (model.optional.reporterOutput e base)
          (model.optional.reporterOutput_measurable e base)
          (model.optional.policy.baseOnlyLaw e base))) /\
      (∀ e base, model.reportRequired.operationalTestBlank e base) :=
  ⟨fun e base =>
      model.optional.operationalTestBlank_of_latent_or_observable
        hOptionalFair e base,
    fun e base =>
      model.reportRequired.operationalTestBlank_of_latent_or_observable
        hReportRequiredFair e base⟩

end LG21ClarifiedTheorem32Model

end

end LG21TestOptionalPolicies
