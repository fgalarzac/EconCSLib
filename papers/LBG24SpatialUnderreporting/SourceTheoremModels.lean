import LBG24SpatialUnderreporting.CausalStoppingEndpointTrace
import LBG24SpatialUnderreporting.CorrectedTheorem2Causal
import LBG24SpatialUnderreporting.Lemma1MarkedPoissonThinning

/-!
# Source-shaped theorem models for LBG24

This module records the semantic model readings used for the two named
stochastic results in the paper.  The models deliberately expose primitive
policy and marked-process laws; neither contains an Eq. (8), Poisson-process,
or law-of-large-numbers conclusion as a field.

For Appendix Theorem 2, the main-text wording says that the endpoint is
independent of the selected start conditional on the reports available at the
endpoint, and the application calls the end rule a stopping-times assumption
(`source.txt:285-323`, `source.txt:2437-2467`).  The finite model below is the
corresponding rate-free causal transition semantics.  A response kernel sees
only the visible report prefix, then races a fresh next-report gap.  The
canonical construction exposes one terminal endpoint after the observed
branch is selected.

For Lemma 1, the source's steady-state argument states a latent Poisson birth
process, independent reporting marks, and the resulting conditional binomial
thinning law (`source.txt:1660-1770`).  The model below makes those primitive
laws explicit and derives the observed Poisson process and unit-window LLN.
-/

namespace LBG24SpatialUnderreporting

open Filter MeasureTheory ProbabilityTheory
open EconCSLib.Probability.PoissonProcess
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

/-! ## Appendix Theorem 2 -/

/--
The source-level finite causal stopping-policy reading of Appendix Theorem 2.

`endpointResponse j` is a rate-free conditional law for an immediate endpoint
response after exactly `j` visible post-start report epochs.  Its domain is the
visible prefix itself, so it cannot inspect a future report gap.  This is the
formal content of the main theorem's "conditional on reports observed up to
that time" language, rather than the stronger global vector of counterfactual
endpoint clocks used by the retired resampled-clock route.
-/
structure AppendixTheorem2CausalStoppingSourceModel (count : ℕ) where
  /-- The selected-start likelihood contribution after conditioning on the
  pre-start report history.  It has no reporting-rate argument. -/
  selectedStartLikelihood : ℝ≥0∞
  /-- The immediate endpoint-response law at each live report prefix. -/
  endpointResponse : ∀ j : Fin (count + 1), Kernel (Fin j.1 → ℝ) ℝ
  endpointResponse_isMarkov : ∀ j, IsMarkovKernel (endpointResponse j)
  /-- Responses are remaining times from the current live prefix. -/
  endpointResponse_nonnegative_support : ∀ j history,
    endpointResponse j history (Set.Iio (0 : ℝ)) = 0
  /-- Measurability needed to compose the finite sequence of live decisions. -/
  responseSurvival_measurable : ∀ i : Fin count,
    Measurable (fun gaps : Fin count → ℝ =>
      endpointResponse i.castSucc (finiteArrivalPrefix gaps i.castSucc)
        (Set.Ioi (gaps i)))

namespace AppendixTheorem2CausalStoppingSourceModel

variable {count : ℕ}

/-- Convert the source causal policy into the finite kernel model used by the
checked likelihood calculation.  This is a structural translation of the
visible source semantics, not a likelihood equality supplied as a premise. -/
def toKernelModel
    (M : AppendixTheorem2CausalStoppingSourceModel count) :
    CollapsedFiniteStageEndpointKernelModel count where
  startWeight := M.selectedStartLikelihood
  endKernel := M.endpointResponse
  endKernel_isMarkov := M.endpointResponse_isMarkov
  endKernel_nonnegative_support := M.endpointResponse_nonnegative_support
  stageSurvival_measurable := M.responseSurvival_measurable

/-- The generated observed branch has one absolute endpoint coordinate. -/
def oneEndpointObservationLaw
    (M : AppendixTheorem2CausalStoppingSourceModel count) (rate : ℝ) :
    Measure ((Fin count → ℝ) × ℝ) :=
  M.toKernelModel.canonicalSingleEndpointTraceLaw rate

/-- The relative endpoint observation law associated with the same causal
policy. -/
def relativeEndpointObservationLaw
    (M : AppendixTheorem2CausalStoppingSourceModel count) (rate : ℝ) :
    Measure ((Fin count → ℝ) × ℝ) :=
  M.toKernelModel.collapsedObservationLaw rate

/-- Integrating the auxiliary live-policy draws leaves the single realized
endpoint law.  This is the one-endpoint coherence theorem used by the source
model; it does not equate any counterfactual response draw with `E`. -/
theorem oneEndpointObservationLaw_eq_map_relativeEndpointObservationLaw
    (M : AppendixTheorem2CausalStoppingSourceModel count)
    {rate : ℝ} (rate_pos : 0 < rate) :
    M.oneEndpointObservationLaw rate =
      Measure.map CollapsedFiniteStageEndpointKernelModel.absoluteEndpointTransform
        (M.relativeEndpointObservationLaw rate) := by
  exact M.toKernelModel.canonicalSingleEndpointTraceLaw_eq_map_collapsedObservationLaw
    rate_pos

/-- A density presentation of the source's printed `h_m(e)` notation.  The
underlying stopping-policy model remains kernel-valued, so applications with
an endpoint atom can still use `toKernelModel`; this presentation is exactly
the absolutely-continuous branch in which the source writes a point density. -/
structure EndpointDensityPresentation
    (M : AppendixTheorem2CausalStoppingSourceModel count) where
  endpointDensity : ∀ j : Fin (count + 1), (Fin j.1 → ℝ) → ℝ → ℝ≥0∞
  endpointDensity_measurable : ∀ j,
    Measurable (Function.uncurry (endpointDensity j))
  endpointResponse_eq_withDensity : ∀ j,
    M.endpointResponse j = Kernel.withDensity
      (Kernel.const (Fin j.1 → ℝ) (volume : Measure ℝ)) (endpointDensity j)
  terminalDensity_measurable :
    Measurable (fun p : (Fin count → ℝ) × ℝ =>
      endpointDensity (Fin.last count)
        (finiteArrivalPrefix p.1 (Fin.last count)) p.2)

/-- The density branch of the causal stopping-policy model used for the
source's displayed Eq. (8) likelihood. -/
def EndpointDensityPresentation.toDensityModel
    (M : AppendixTheorem2CausalStoppingSourceModel count)
    (D : EndpointDensityPresentation M) :
    CollapsedFiniteStageEndpointModel count where
  startWeight := M.selectedStartLikelihood
  endKernel := M.endpointResponse
  endKernel_isMarkov := M.endpointResponse_isMarkov
  endDensity := D.endpointDensity
  endDensity_measurable := D.endpointDensity_measurable
  endKernel_eq_withDensity := D.endpointResponse_eq_withDensity
  stageSurvival_measurable := M.responseSurvival_measurable
  terminalDensity_measurable := D.terminalDensity_measurable

/-- The fixed-history likelihood density of the source causal policy in its
printed density presentation. -/
def conditionalLikelihood
    (T : OrderedFiniteJumpTimeline)
    (M : AppendixTheorem2CausalStoppingSourceModel T.count)
    (D : EndpointDensityPresentation M) (rate : ℝ) : ℝ :=
  CollapsedFiniteStageEndpointModel.theorem2CausalConditionalLikelihood T
    (EndpointDensityPresentation.toDensityModel M D) rate

/-- The rate-free source residual in the corrected Eq. (8) factorization. -/
def rateFreeResidual
    (T : OrderedFiniteJumpTimeline)
    (M : AppendixTheorem2CausalStoppingSourceModel T.count)
    (D : EndpointDensityPresentation M) : ℝ :=
  FiniteStageCausalEndpointProfile.correctedResidual
    (CollapsedFiniteStageEndpointModel.toFiniteStageCausalEndpointProfile
      (T := T) (EndpointDensityPresentation.toDensityModel M D))

/--
Appendix Theorem 2 / Eq. (8) for the source causal stopping-policy model.

The policy is shared across all `rate` values because it is a single model
argument with no rate parameter.  Therefore the residual is genuinely
rate-free.  The source proof's two algebra corrections remain visible through
the checked `correctedResidual`: the first gap starts at `S`, and the Poisson
PMF conversion uses `count! / (E-S)^count`.
-/
theorem conditionalLikelihood_factorizes_eq8
    (M : AppendixTheorem2CausalStoppingSourceModel T.count)
    (D : EndpointDensityPresentation M)
    {rate : ℝ} (rate_pos : 0 < rate)
    (exposure_pos : 0 < T.window.exposure) :
    conditionalLikelihood T M D rate =
      rateFreeResidual T M D *
        sourcePoissonPMF rate T.window.exposure T.count := by
  simpa [conditionalLikelihood, rateFreeResidual] using
    (CollapsedFiniteStageEndpointModel.theorem2CausalConditionalLikelihood_factorizes_corrected_eq8
      T (EndpointDensityPresentation.toDensityModel M D) rate_pos exposure_pos)

end AppendixTheorem2CausalStoppingSourceModel

/-! ## Lemma 1 and Proposition 1 -/

/--
The source's duration law is a probability density on nonnegative durations.
The formal function is total on `ℝ`, while the restricted measure represents
the source domain `[0,∞)`. Integrability includes the required a.e.
measurability; values outside that domain carry no source meaning.
-/
structure ContinuousDurationDensitySourceCondition
    (durationDensity : ℝ → ℝ) : Prop where
  integrable :
    Integrable durationDensity (volume.restrict (Set.Ici (0 : ℝ)))
  nonnegative_ae :
    ∀ᵐ t ∂(volume.restrict (Set.Ici (0 : ℝ))), 0 ≤ durationDensity t
  integral_eq_one :
    (∫ t, durationDensity t ∂(volume.restrict (Set.Ici (0 : ℝ)))) = 1

namespace ContinuousDurationDensitySourceCondition

variable {durationDensity : ℝ → ℝ}

/-- A genuine duration density makes the displayed retention expression at
most one. This is the source probability fact used by the Proposition 1
construction, rather than an independent numerical premise. -/
theorem firstReportProbability_le_one
    (H : ContinuousDurationDensitySourceCondition durationDensity)
    (reportingRate : ℝ) :
    continuousDurationFirstReportProbability reportingRate durationDensity ≤ 1 := by
  have h_noReport_nonneg :
      0 ≤ ∫ t,
        durationDensity t * noArrivalProb reportingRate t
          ∂(volume.restrict (Set.Ici (0 : ℝ))) := by
    apply MeasureTheory.integral_nonneg_of_ae
    filter_upwards [H.nonnegative_ae] with t ht
    exact mul_nonneg ht (noArrivalProb_nonneg reportingRate t)
  dsimp [continuousDurationFirstReportProbability,
    continuousDurationNoReportProbability]
  exact sub_le_self 1 h_noReport_nonneg

end ContinuousDurationDensitySourceCondition

/--
The source-level birth-cohort model used in the cumulative-intensity proof of
Lemma 1.  The source proof gives the per-incident report-count law
`m(t) ~ Poisson (integral_0^t lambda_theta(u) du)` and independent reporting
across incidents, then conditions the count of eventually reported incidents
born in a window on the birth count in that same window.  This model records
that independently marked latent incident process, together with the source
calculation of its eventual-report probability.  It does not take the retained
birth process as a field.

It deliberately does not identify a retained birth with a first-report arrival
in a calendar-time window.  That stronger reading needs a two-sided stationary
marked-displacement construction and an explicit duration/report-path
independence condition.

The scalar-rate model below is retained for Proposition 1, whose stated
setting is explicitly time homogeneous.
-/
structure Lemma1CumulativeIntensitySteadyStateDurationSourceModel
    (Omega : Type*) [MeasurableSpace Omega] (P : Measure Omega) where
  incidentRate : ℝ
  /-- The source's possibly time-inhomogeneous per-incident reporting rate. -/
  reportingIntensity : ℝ → ℝ
  durationDensity : ℝ → ℝ
  /-- `f` is the source duration probability density on `[0,infinity)`. -/
  durationDensity_source : ContinuousDurationDensitySourceCondition durationDensity
  /-- The latent Poisson incidents and their independent eventual-report marks. -/
  markedProcess : Lemma1MarkedPoissonThinning.MarkedPoissonReportingProcess Omega P
  latent_rate_eq_incidentRate : markedProcess.latentProcess.rate = incidentRate
  /--
  The source calculation
  `Pr[at least one report before T] =
    1 - integral exp (- integral_0^t lambda_theta(u) du) f(t) dt`.

  This is the explicitly source-anchored bridge from the per-incident Poisson
  report paths to the iid eventual-report mark.  It is not an observed-process
  conclusion.
  -/
  retention_probability_eq_cumulative_firstReportProbability :
    markedProcess.detectionProbability =
      continuousDurationFirstReportProbabilityOfCumulativeIntensity
        (fun t => ∫ u in (0 : ℝ)..t, reportingIntensity u) durationDensity

namespace Lemma1CumulativeIntensitySteadyStateDurationSourceModel

variable {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}

/-- The full cumulative-intensity observed rate displayed in source Lemma 1. -/
def observedIncidentRate
    (M : Lemma1CumulativeIntensitySteadyStateDurationSourceModel Omega P) : ℝ :=
  continuousDurationObservedIncidentRateOfCumulativeIntensity
    M.incidentRate (fun t => ∫ u in (0 : ℝ)..t, M.reportingIntensity u)
    M.durationDensity

/--
The observed unique-incident process follows from latent Poisson incidents and
the source's iid eventual-report marks.  This proves the full
cumulative-intensity Lemma 1 rate, including the homogeneous case as a
specialization.
-/
theorem observed_process_is_homogeneous_poisson
    (M : Lemma1CumulativeIntensitySteadyStateDurationSourceModel Omega P) :
    ∃ observedProcess : ForwardHomogeneousPoissonCountingProcessByLaw Omega P,
      observedProcess.count = M.markedProcess.observedCount ∧
      observedProcess.rate = M.observedIncidentRate := by
  rcases M.markedProcess.observed_process_is_homogeneous_poisson with
    ⟨observedProcess, hcount, hrate⟩
  refine ⟨observedProcess, hcount, ?_⟩
  rw [hrate, M.latent_rate_eq_incidentRate,
    M.retention_probability_eq_cumulative_firstReportProbability]
  rfl

/-- The retained-birth count in the source proof's unit-window cohort. -/
def retainedBirthCohortCount
    (M : Lemma1CumulativeIntensitySteadyStateDurationSourceModel Omega P)
    (n : ℕ) (omega : Omega) : ℕ :=
  ∑ i ∈ Finset.range n,
    M.markedProcess.toObservedForwardPoissonProcess.unitIntervalCount i omega

/--
The same cohort model yields the unit-window strong law at the full
cumulative-intensity retained-birth rate.  Proposition 1 only uses its
homogeneous specialization.
-/
theorem retainedBirthCohortCount_real_strongLaw
    (M : Lemma1CumulativeIntensitySteadyStateDurationSourceModel Omega P) :
    ∀ᵐ omega ∂P,
      Tendsto (fun n : ℕ =>
        (M.retainedBirthCohortCount n omega : ℝ) / n)
        atTop (nhds M.observedIncidentRate) := by
  filter_upwards [M.markedProcess.observed_unitIntervalCount_real_strongLaw]
    with omega homega
  simpa [retainedBirthCohortCount, observedIncidentRate,
    continuousDurationObservedIncidentRateOfCumulativeIntensity,
    M.latent_rate_eq_incidentRate,
    M.retention_probability_eq_cumulative_firstReportProbability] using homega

end Lemma1CumulativeIntensitySteadyStateDurationSourceModel

/--
The source-level steady-state model for Lemma 1.  The marked process contains
the latent Poisson birth path and the independently marked observed path.  The
only duration-specific bridge is the source's displayed probability of at
least one report before an iid duration ends; the observed Poisson process and
LLN are derived below.
-/
structure Lemma1SteadyStateDurationSourceModel
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) where
  incidentRate : ℝ
  reportingRate : ℝ
  durationDensity : ℝ → ℝ
  /-- `f` is the source duration probability density on `[0,∞)`. -/
  durationDensity_source : ContinuousDurationDensitySourceCondition durationDensity
  markedProcess : Lemma1MarkedPoissonThinning.MarkedPoissonReportingProcess Ω P
  latent_rate_eq_incidentRate : markedProcess.latentProcess.rate = incidentRate
  /-- Audited source-model bridge for the source's calculation
  `Pr[at least one report before T] = 1 - integral exp(-lambda t) f(t) dt`.
  The marked-process interface abstracts the lower-level per-incident report
  paths, so this equality is an explicit source premise with its own anchor,
  not an observed-process conclusion or a certificate of one. -/
  retention_probability_eq_firstReportProbability :
    markedProcess.detectionProbability =
      continuousDurationFirstReportProbability reportingRate durationDensity

namespace Lemma1SteadyStateDurationSourceModel

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The source's displayed steady-state observed incident rate. -/
def observedIncidentRate
    (M : Lemma1SteadyStateDurationSourceModel Ω P) : ℝ :=
  continuousDurationObservedIncidentRate
    M.incidentRate M.reportingRate M.durationDensity

/-- The observed unique-incident process is derived from the latent process
and independent marks, at exactly the source rate. -/
theorem observed_process_is_homogeneous_poisson
    (M : Lemma1SteadyStateDurationSourceModel Ω P) :
    ∃ observedProcess : ForwardHomogeneousPoissonCountingProcessByLaw Ω P,
      observedProcess.count = M.markedProcess.observedCount ∧
      observedProcess.rate = M.observedIncidentRate := by
  rcases M.markedProcess.observed_process_is_homogeneous_poisson with
    ⟨observedProcess, hcount, hrate⟩
  refine ⟨observedProcess, hcount, ?_⟩
  rw [hrate, M.latent_rate_eq_incidentRate,
    M.retention_probability_eq_firstReportProbability]
  rfl

/-- The source's large-time count is the sum of the observed unit-window
counts used in Appendix B.1. -/
def observedUniqueIncidentCount
    (M : Lemma1SteadyStateDurationSourceModel Ω P)
    (n : ℕ) (omega : Ω) : ℕ :=
  ∑ i ∈ Finset.range n,
    M.markedProcess.toObservedForwardPoissonProcess.unitIntervalCount i omega

/-- Proposition 1's stated unit-window LLN follows from the derived observed
Poisson process, with the source duration-law rate substituted. -/
theorem observedUniqueIncidentCount_real_strongLaw
    (M : Lemma1SteadyStateDurationSourceModel Ω P) :
    ∀ᵐ omega ∂P,
      Tendsto (fun n : ℕ =>
        (M.observedUniqueIncidentCount n omega : ℝ) / n)
        atTop (nhds M.observedIncidentRate) := by
  filter_upwards [M.markedProcess.observed_unitIntervalCount_real_strongLaw]
    with omega homega
  simpa [observedUniqueIncidentCount, observedIncidentRate,
    continuousDurationObservedIncidentRate,
    M.latent_rate_eq_incidentRate,
    M.retention_probability_eq_firstReportProbability] using homega

/-- Two source models with different reporting rates but the same displayed
observed rate have observationally indistinguishable homogeneous-Poisson
unique-incident processes at the level used by Proposition 1. -/
theorem compensating_models_have_equal_observed_process_rates
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    (M₁ : Lemma1SteadyStateDurationSourceModel Ω₁ P₁)
    (M₂ : Lemma1SteadyStateDurationSourceModel Ω₂ P₂)
    (reporting_rates_ne : M₁.reportingRate ≠ M₂.reportingRate)
    (observed_rates_eq : M₁.observedIncidentRate = M₂.observedIncidentRate) :
    M₁.reportingRate ≠ M₂.reportingRate ∧
      ∃ observedProcess₁ : ForwardHomogeneousPoissonCountingProcessByLaw Ω₁ P₁,
        ∃ observedProcess₂ : ForwardHomogeneousPoissonCountingProcessByLaw Ω₂ P₂,
          observedProcess₁.count = M₁.markedProcess.observedCount ∧
          observedProcess₂.count = M₂.markedProcess.observedCount ∧
          observedProcess₁.rate = observedProcess₂.rate := by
  rcases M₁.observed_process_is_homogeneous_poisson with
    ⟨observedProcess₁, hcount₁, hrate₁⟩
  rcases M₂.observed_process_is_homogeneous_poisson with
    ⟨observedProcess₂, hcount₂, hrate₂⟩
  refine ⟨reporting_rates_ne, observedProcess₁, observedProcess₂,
    hcount₁, hcount₂, ?_⟩
  rw [hrate₁, hrate₂, observed_rates_eq]

/--
Construct the two source-steady-state models used by Proposition 1.  Distinct
reporting rates are paired with the compensating incident rates from the
source's displayed formula, so both derived observed processes have the same
rate.  This is an existence construction, not an equality of hidden model
records or a replay of a conclusion-bearing certificate.
-/
theorem exists_compensating_source_models
    (durationDensity : ℝ → ℝ)
    (durationDensity_source :
      ContinuousDurationDensitySourceCondition durationDensity)
    {observedRate reportingRate₁ reportingRate₂ : ℝ}
    (reporting_rates_ne : reportingRate₁ ≠ reportingRate₂)
    (observedRate_pos : 0 < observedRate)
    (retention₁_pos :
      0 < continuousDurationFirstReportProbability reportingRate₁ durationDensity)
    (retention₁_le_one :
      continuousDurationFirstReportProbability reportingRate₁ durationDensity ≤ 1)
    (retention₂_pos :
      0 < continuousDurationFirstReportProbability reportingRate₂ durationDensity)
    (retention₂_le_one :
      continuousDurationFirstReportProbability reportingRate₂ durationDensity ≤ 1) :
    reportingRate₁ ≠ reportingRate₂ ∧
      ∃ (Ω₁ : Type) (mΩ₁ : MeasurableSpace Ω₁) (P₁ : Measure Ω₁)
          (M₁ : @Lemma1SteadyStateDurationSourceModel Ω₁ mΩ₁ P₁),
        ∃ (Ω₂ : Type) (mΩ₂ : MeasurableSpace Ω₂) (P₂ : Measure Ω₂)
          (M₂ : @Lemma1SteadyStateDurationSourceModel Ω₂ mΩ₂ P₂),
          M₁.reportingRate = reportingRate₁ ∧
          M₂.reportingRate = reportingRate₂ ∧
          M₁.observedIncidentRate = observedRate ∧
          M₂.observedIncidentRate = observedRate ∧
          ∃ observedProcess₁ :
              @ForwardHomogeneousPoissonCountingProcessByLaw Ω₁ mΩ₁ P₁,
            ∃ observedProcess₂ :
                @ForwardHomogeneousPoissonCountingProcessByLaw Ω₂ mΩ₂ P₂,
              observedProcess₁.count = M₁.markedProcess.observedCount ∧
              observedProcess₂.count = M₂.markedProcess.observedCount ∧
              observedProcess₁.rate = observedProcess₂.rate := by
  let retention₁ :=
    continuousDurationFirstReportProbability reportingRate₁ durationDensity
  let retention₂ :=
    continuousDurationFirstReportProbability reportingRate₂ durationDensity
  let incidentRate₁ := observedRate / retention₁
  let incidentRate₂ := observedRate / retention₂
  have incidentRate₁_pos : 0 < incidentRate₁ :=
    div_pos observedRate_pos retention₁_pos
  have incidentRate₂_pos : 0 < incidentRate₂ :=
    div_pos observedRate_pos retention₂_pos
  rcases
      Lemma1MarkedPoissonThinning.MarkedPoissonReportingProcess.exists_markedPoissonReportingProcess
        incidentRate₁ retention₁ incidentRate₁_pos retention₁_pos retention₁_le_one with
    ⟨Ω₁, mΩ₁, P₁, marked₁, latent₁_rate, marked₁_retention⟩
  rcases
      Lemma1MarkedPoissonThinning.MarkedPoissonReportingProcess.exists_markedPoissonReportingProcess
        incidentRate₂ retention₂ incidentRate₂_pos retention₂_pos retention₂_le_one with
    ⟨Ω₂, mΩ₂, P₂, marked₂, latent₂_rate, marked₂_retention⟩
  let M₁ : @Lemma1SteadyStateDurationSourceModel Ω₁ mΩ₁ P₁ :=
    { incidentRate := incidentRate₁
      reportingRate := reportingRate₁
      durationDensity := durationDensity
      durationDensity_source := durationDensity_source
      markedProcess := marked₁
      latent_rate_eq_incidentRate := latent₁_rate
      retention_probability_eq_firstReportProbability := by
        simpa [retention₁] using marked₁_retention }
  let M₂ : @Lemma1SteadyStateDurationSourceModel Ω₂ mΩ₂ P₂ :=
    { incidentRate := incidentRate₂
      reportingRate := reportingRate₂
      durationDensity := durationDensity
      durationDensity_source := durationDensity_source
      markedProcess := marked₂
      latent_rate_eq_incidentRate := latent₂_rate
      retention_probability_eq_firstReportProbability := by
        simpa [retention₂] using marked₂_retention }
  have observed₁_rate : M₁.observedIncidentRate = observedRate := by
    change incidentRate₁ * retention₁ = observedRate
    exact div_mul_cancel₀ observedRate (ne_of_gt retention₁_pos)
  have observed₂_rate : M₂.observedIncidentRate = observedRate := by
    change incidentRate₂ * retention₂ = observedRate
    exact div_mul_cancel₀ observedRate (ne_of_gt retention₂_pos)
  rcases M₁.observed_process_is_homogeneous_poisson with
    ⟨observedProcess₁, observed₁_count, observedProcess₁_rate⟩
  rcases M₂.observed_process_is_homogeneous_poisson with
    ⟨observedProcess₂, observed₂_count, observedProcess₂_rate⟩
  refine ⟨reporting_rates_ne, Ω₁, mΩ₁, P₁, M₁, Ω₂, mΩ₂, P₂, M₂,
    rfl, rfl, observed₁_rate, observed₂_rate,
    observedProcess₁, observedProcess₂, observed₁_count, observed₂_count, ?_⟩
  rw [observedProcess₁_rate, observedProcess₂_rate,
    observed₁_rate, observed₂_rate]

end Lemma1SteadyStateDurationSourceModel

end

end LBG24SpatialUnderreporting
