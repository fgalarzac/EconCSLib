import LG21TestOptionalPolicies.SelectedConditionalExpectation
import LG21TestOptionalPolicies.ContinuousObservedAccessSequentialActionBridge
import Mathlib.Probability.Kernel.Posterior

/-!
# Public-action PBO bridge for report-required LG21 testing

In the report-required protocol, the school observes a reported score exactly
when the student's public taking rule says that they take.  This module keeps
that fact at the measure level.  In particular, it conditions on the observed
report action and the *public decision function*, not on an externally supplied
or directly observed latent-skill label.

The result is source-neutral and fixes one already-observed base-feature fibre.
A literal LG21 Gaussian source bridge must instantiate `rawLaw`, prove the
displayed positive-fibre fact from its nondegenerate Gaussian law, and then
connect the resulting conditional expectation to the paper's PBO policy.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

/-! ## Public report-required action events -/

/--
The score/skill event inferred from a public report-required taking rule.
The school does not observe `skill` directly.  It infers this event from a
reported score together with the known decision function.
-/
def lg21ReportRequiredPublicReporterEvent
    (takeDecision : ℝ → Bool) : Set (ℝ × ℝ) :=
  {scoreSkill | takeDecision scoreSkill.2 = true}

/-- The public reporter event is measurable when the taking rule is measurable. -/
theorem lg21ReportRequiredPublicReporterEvent_measurable
    (takeDecision : ℝ → Bool) (htakeDecision : Measurable takeDecision) :
    MeasurableSet (lg21ReportRequiredPublicReporterEvent takeDecision) := by
  change MeasurableSet
    ((fun scoreSkill : ℝ × ℝ => takeDecision scoreSkill.2) ⁻¹'
      ({true} : Set Bool))
  exact (measurableSet_singleton true).preimage
    (htakeDecision.comp measurable_snd)

/--
If reporting is required after taking, the actually observed reporter event is
the preimage of the public score/skill selection event.  This is the semantic
link that prevents a later proof from conditioning on a hidden cohort name.
-/
theorem lg21_reportRequired_observedReporter_eq_publicEvent_preimage
    {Omega : Type*} [MeasurableSpace Omega]
    (score skill : Omega → ℝ) (takeDecision : ℝ → Bool)
    (observedReport : Omega → Bool)
    (hrequired : ∀ omega, observedReport omega = takeDecision (skill omega)) :
    {omega | observedReport omega = true} =
      (fun omega => (score omega, skill omega)) ⁻¹'
        lg21ReportRequiredPublicReporterEvent takeDecision := by
  ext omega
  change observedReport omega = true ↔ takeDecision (skill omega) = true
  rw [hrequired omega]

/-! ## Actual selected conditional PBO -/

/--
For a positive-mass public report-required action profile, the conditional
expectation of skill after observing a report and score is the mean of an
explicit raw score-posterior kernel restricted to the public taking event.

The conclusion is almost everywhere under the *actual reporter population*.
It neither labels a student with a latent cohort nor assigns a value to a
zero-mass reporter branch.  The raw posterior is an explicit Markov kernel
with an exact joint-law factorization, rather than an arbitrary pointwise
version of `condDistrib`.  The `hpositiveFibre` premise is deliberately
visible: it is the condition needed to give the selected posterior kernel a
probability value at every score.  In the intended nondegenerate Gaussian
instantiation it is proved for the explicit Gaussian posterior kernel, not
inferred from an a.e. conditional-distribution theorem.
-/
theorem lg21_reportRequired_publicAction_condExp_eq_selectedPosteriorMean_ae
    {Omega : Type*} [MeasurableSpace Omega]
    (rawLaw : Measure Omega) [IsProbabilityMeasure rawLaw] [IsFiniteMeasure rawLaw]
    (score skill : Omega → ℝ)
    (hscore : Measurable score) (hskill : Measurable skill)
    (rawPosterior : Kernel ℝ ℝ) [IsMarkovKernel rawPosterior]
    (hrawJoint :
      rawLaw.map (fun omega => (score omega, skill omega)) =
        rawLaw.map score ⊗ₘ rawPosterior)
    (takeDecision : ℝ → Bool) (observedReport : Omega → Bool)
    (htakeDecision : Measurable takeDecision)
    (hrequired : ∀ omega, observedReport omega = takeDecision (skill omega))
    (hpositive : 0 < rawLaw {omega | observedReport omega = true})
    (hpositiveFibre :
      ∀ observedScore, selectionMass rawPosterior
        (lg21ReportRequiredPublicReporterEvent takeDecision) observedScore ≠ 0)
    (hintegrable :
      Integrable skill
        (lg21NormalizedRestriction rawLaw
          {omega | observedReport omega = true})) :
    let reporterLaw := lg21NormalizedRestriction rawLaw
      {omega | observedReport omega = true}
    reporterLaw[skill | MeasurableSpace.comap score inferInstance] =ᵐ[reporterLaw]
      fun omega => ∫ latentSkill, latentSkill ∂
        selectedNormalizedKernel rawPosterior
          (lg21ReportRequiredPublicReporterEvent takeDecision) (score omega) := by
  intro reporterLaw
  let publicEvent : Set (ℝ × ℝ) :=
    lg21ReportRequiredPublicReporterEvent takeDecision
  let rawScoreLaw : Measure ℝ := rawLaw.map score
  let selectedPosterior : Kernel ℝ ℝ :=
    selectedNormalizedKernel rawPosterior publicEvent
  let scoreSkill : Omega → ℝ × ℝ := fun omega => (score omega, skill omega)
  have hscoreSkill : Measurable scoreSkill := hscore.prodMk hskill
  have hpublicEvent : MeasurableSet publicEvent := by
    simpa [publicEvent] using
      (lg21ReportRequiredPublicReporterEvent_measurable
        takeDecision htakeDecision)
  have hactionEvent :
      {omega | observedReport omega = true} = scoreSkill ⁻¹' publicEvent := by
    simpa [scoreSkill, publicEvent] using
      (lg21_reportRequired_observedReporter_eq_publicEvent_preimage
        score skill takeDecision observedReport hrequired)
  have hpositiveAction : rawLaw (scoreSkill ⁻¹' publicEvent) ≠ 0 := by
    rw [← hactionEvent]
    exact ne_of_gt hpositive
  letI : IsProbabilityMeasure reporterLaw := by
    dsimp [reporterLaw]
    apply lg21NormalizedRestriction_isProbability
    · exact ne_of_gt hpositive
    · exact measure_ne_top _ _
  letI : IsFiniteMeasure reporterLaw := ⟨by simp⟩
  letI : IsSFiniteKernel selectedPosterior := by
    dsimp [selectedPosterior]
    exact selectedNormalizedKernel_isSFinite (κ := rawPosterior)
      (by simpa [publicEvent] using hpositiveFibre)
  letI : IsMarkovKernel selectedPosterior := by
    dsimp [selectedPosterior]
    apply selectedNormalizedKernel_isMarkov hpublicEvent
    simpa [publicEvent] using hpositiveFibre
  letI : SFinite (selectedBase rawScoreLaw rawPosterior publicEvent) := by
    unfold selectedBase
    infer_instance
  letI : SFinite (normalizedSelectedBase rawScoreLaw rawPosterior publicEvent) := by
    unfold normalizedSelectedBase
    infer_instance
  have hrawFactor :
      rawLaw.map scoreSkill = rawScoreLaw ⊗ₘ rawPosterior := by
    simpa [scoreSkill, rawScoreLaw] using hrawJoint
  have hselectedPair :
      reporterLaw.map scoreSkill =
        lg21NormalizedRestriction (rawScoreLaw ⊗ₘ rawPosterior) publicEvent := by
    calc
      reporterLaw.map scoreSkill =
          (lg21NormalizedRestriction rawLaw (scoreSkill ⁻¹' publicEvent)).map
            scoreSkill := by
              rw [show reporterLaw =
                  lg21NormalizedRestriction rawLaw (scoreSkill ⁻¹' publicEvent) by
                    rw [show reporterLaw = lg21NormalizedRestriction rawLaw
                      {omega | observedReport omega = true} by rfl, hactionEvent]]
      _ = lg21NormalizedRestriction (rawLaw.map scoreSkill) publicEvent :=
        LG21ObservedAccessSourceConditionalKernel.normalizedRestriction_map_preimage
          rawLaw scoreSkill hscoreSkill publicEvent hpublicEvent
      _ = lg21NormalizedRestriction (rawScoreLaw ⊗ₘ rawPosterior) publicEvent := by
        rw [hrawFactor]
  have hselectedFactor :
      lg21NormalizedRestriction (rawScoreLaw ⊗ₘ rawPosterior) publicEvent =
        normalizedSelectedBase rawScoreLaw rawPosterior publicEvent ⊗ₘ
          selectedPosterior := by
    dsimp [selectedPosterior]
    exact normalizedRestriction_compProd_selectedNormalizedKernel
      (μ := rawScoreLaw) (κ := rawPosterior) hpublicEvent
      (by simpa [publicEvent] using hpositiveFibre)
  have hreporterScoreLaw :
      reporterLaw.map score =
        normalizedSelectedBase rawScoreLaw rawPosterior publicEvent := by
    calc
      reporterLaw.map score = (reporterLaw.map scoreSkill).map Prod.fst := by
        rw [Measure.map_map measurable_fst hscoreSkill]
        rfl
      _ = (lg21NormalizedRestriction (rawScoreLaw ⊗ₘ rawPosterior)
          publicEvent).map Prod.fst := by rw [hselectedPair]
      _ = (normalizedSelectedBase rawScoreLaw rawPosterior publicEvent ⊗ₘ
          selectedPosterior).map Prod.fst := by rw [hselectedFactor]
      _ = normalizedSelectedBase rawScoreLaw rawPosterior publicEvent :=
        Measure.fst_compProd _ _
  have hselectedJoint :
      reporterLaw.map scoreSkill = reporterLaw.map score ⊗ₘ selectedPosterior := by
    rw [hselectedPair, hselectedFactor, hreporterScoreLaw]
  have hcondDistrib :
      condDistrib skill score reporterLaw =ᵐ[reporterLaw.map score]
        selectedPosterior := by
    exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
      hscore hskill hselectedJoint
  have hcondExp := condExp_ae_eq_integral_condDistrib' hscore hintegrable
  have hcondDistribPullback :
      ∀ᵐ omega ∂reporterLaw,
        condDistrib skill score reporterLaw (score omega) =
          selectedPosterior (score omega) := by
    exact ae_of_ae_map hscore.aemeasurable hcondDistrib
  filter_upwards [hcondExp, hcondDistribPullback] with omega hExp hKernel
  rw [hExp, hKernel]

/-! ## Canonical selected signal posterior -/

/--
The posterior-kernel form of the report-required public-action bridge.

Here `signal` is the literal kernel by which a latent skill generates a test
score, and `selectedSkillLaw` is the latent law induced by the public taking
rule.  The caller supplies the exact selected joint-law factorization; for a
Gaussian signal it follows from the source action event and
`compProd_posterior_eq_map_swap`.  Unlike fibrewise normalization of an
arbitrary raw `condDistrib`, this theorem has no all-score positivity premise:
`signal†selectedSkillLaw` is a canonical Markov posterior kernel.

The selection evidence remains tied to the observable report action through
`hrequired`; the theorem does not condition on a hidden named cohort.
-/
theorem lg21_reportRequired_publicAction_condExp_eq_signalPosteriorMean_ae
    {Omega : Type*} [MeasurableSpace Omega]
    (rawLaw : Measure Omega) [IsProbabilityMeasure rawLaw] [IsFiniteMeasure rawLaw]
    (score skill : Omega → ℝ)
    (hscore : Measurable score) (hskill : Measurable skill)
    (signal : Kernel ℝ ℝ) [IsFiniteKernel signal]
    (selectedSkillLaw : Measure ℝ) [IsProbabilityMeasure selectedSkillLaw]
    (takeDecision : ℝ → Bool) (observedReport : Omega → Bool)
    (hrequired : ∀ omega, observedReport omega = takeDecision (skill omega))
    (hpositive : 0 < rawLaw {omega | observedReport omega = true})
    (hselectedJoint :
      (lg21NormalizedRestriction rawLaw
        ((fun omega => (score omega, skill omega)) ⁻¹'
          lg21ReportRequiredPublicReporterEvent takeDecision)).map
        (fun omega => (score omega, skill omega)) =
      (signal ∘ₘ selectedSkillLaw) ⊗ₘ (signal†selectedSkillLaw))
    (hintegrable : Integrable skill
      (lg21NormalizedRestriction rawLaw {omega | observedReport omega = true})) :
    let reporterLaw := lg21NormalizedRestriction rawLaw
      {omega | observedReport omega = true}
    reporterLaw[skill | MeasurableSpace.comap score inferInstance] =ᵐ[reporterLaw]
      fun omega => ∫ latentSkill, latentSkill ∂
        (signal†selectedSkillLaw) (score omega) := by
  intro reporterLaw
  let publicEvent : Set (ℝ × ℝ) :=
    lg21ReportRequiredPublicReporterEvent takeDecision
  let scoreSkill : Omega → ℝ × ℝ := fun omega => (score omega, skill omega)
  have hscoreSkill : Measurable scoreSkill := hscore.prodMk hskill
  have hactionEvent :
      {omega | observedReport omega = true} = scoreSkill ⁻¹' publicEvent := by
    simpa [scoreSkill, publicEvent] using
      (lg21_reportRequired_observedReporter_eq_publicEvent_preimage
        score skill takeDecision observedReport hrequired)
  letI : IsProbabilityMeasure reporterLaw := by
    dsimp [reporterLaw]
    exact lg21NormalizedRestriction_isProbability rawLaw
      {omega | observedReport omega = true} (ne_of_gt hpositive)
      (measure_ne_top _ _)
  letI : IsFiniteMeasure reporterLaw := ⟨by simp⟩
  let posterior : Kernel ℝ ℝ := signal†selectedSkillLaw
  have hselectedJointReporter :
      reporterLaw.map scoreSkill = (signal ∘ₘ selectedSkillLaw) ⊗ₘ posterior := by
    rw [show reporterLaw = lg21NormalizedRestriction rawLaw
      (scoreSkill ⁻¹' publicEvent) by
      rw [show reporterLaw = lg21NormalizedRestriction rawLaw
        {omega | observedReport omega = true} by rfl, hactionEvent]]
    simpa [scoreSkill, publicEvent, posterior] using hselectedJoint
  have hreporterScoreLaw : reporterLaw.map score = signal ∘ₘ selectedSkillLaw := by
    calc
      reporterLaw.map score = (reporterLaw.map scoreSkill).map Prod.fst := by
        rw [Measure.map_map measurable_fst hscoreSkill]
        rfl
      _ = ((signal ∘ₘ selectedSkillLaw) ⊗ₘ posterior).map Prod.fst := by
        rw [hselectedJointReporter]
      _ = signal ∘ₘ selectedSkillLaw := Measure.fst_compProd _ _
  have hfactor : reporterLaw.map scoreSkill = reporterLaw.map score ⊗ₘ posterior := by
    rw [hselectedJointReporter, hreporterScoreLaw]
  have hcondDistrib :
      condDistrib skill score reporterLaw =ᵐ[reporterLaw.map score] posterior := by
    exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
      hscore hskill hfactor
  have hcondExp := condExp_ae_eq_integral_condDistrib' hscore hintegrable
  have hcondDistribPullback :
      ∀ᵐ omega ∂reporterLaw,
        condDistrib skill score reporterLaw (score omega) =
          posterior (score omega) := by
    exact ae_of_ae_map hscore.aemeasurable hcondDistrib
  filter_upwards [hcondExp, hcondDistribPullback] with omega hExp hKernel
  rw [hExp, hKernel]

end

end LG21TestOptionalPolicies
