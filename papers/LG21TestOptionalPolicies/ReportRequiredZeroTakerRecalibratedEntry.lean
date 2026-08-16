import LG21TestOptionalPolicies.ReportRequiredSelectionAwarePBOBridge
import LG21TestOptionalPolicies.RecalibratedBranchMemberEntry

/-!
# Literal candidate entry at the report-required zero-taker endpoint

This module gives the report-required counterpart of the optional
all-no-reporter source certificate.  A candidate taking branch is evaluated
with the PBOs induced by its own positive source action events.  The
Definition-1 check is pre-score: it compares the candidate no-take value with
the expected reported value before the noisy score is drawn.

The certificate is intentionally a branch-entry object, not a claim that the
candidate is a whole-population equilibrium.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set

/-- The literal source event on which a report-required candidate takes and reports. -/
def lg21ReportRequiredCandidateSourceTakeEvent
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega -> Base) (skill : Omega -> ℝ)
    (candidate : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ) : Set Omega :=
  {omega | candidate.takeDecision (skill omega) (base omega) = true}

/-- The complementary literal source event on which the candidate does not take. -/
def lg21ReportRequiredCandidateSourceNoTakeEvent
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega -> Base) (skill : Omega -> ℝ)
    (candidate : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ) : Set Omega :=
  {omega | candidate.takeDecision (skill omega) (base omega) = false}

/-- The candidate's reported PBO on its own positive taking/reporting law. -/
def LG21ReportRequiredCandidateReportedPBO
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hpublic : Measurable (fun omega => (base omega, (score omega, skill omega))))
    (candidate : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ)
    (hpositive : 0 < sourceLaw
      (lg21ReportRequiredCandidateSourceTakeEvent base skill candidate)) : Prop :=
  let actionLaw :=
    (lg21NormalizedRestriction sourceLaw
      (lg21ReportRequiredCandidateSourceTakeEvent base skill candidate)).map
        (fun omega => (base omega, (score omega, skill omega)))
  letI : IsProbabilityMeasure
      (lg21NormalizedRestriction sourceLaw
        (lg21ReportRequiredCandidateSourceTakeEvent base skill candidate)) :=
    lg21NormalizedRestriction_isProbability sourceLaw _
      (ne_of_gt hpositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure actionLaw :=
    Measure.isProbabilityMeasure_map hpublic.aemeasurable
  letI : IsFiniteMeasure actionLaw := by
    exact ⟨by simp⟩
  ∀ᵐ publicObservation ∂actionLaw.map
      (fun scoreSkill : Base × (ℝ × ℝ) => (scoreSkill.1, scoreSkill.2.1)),
    candidate.reportedPayoff publicObservation.1 publicObservation.2 =
      ∫ latentSkill, latentSkill ∂condDistrib
        (fun scoreSkill : Base × (ℝ × ℝ) => scoreSkill.2.2)
        (fun scoreSkill : Base × (ℝ × ℝ) => (scoreSkill.1, scoreSkill.2.1))
        actionLaw publicObservation

/-- The candidate's no-take PBO on its own positive no-take law. -/
def LG21ReportRequiredCandidateNoTakePBO
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hpublic : Measurable (fun omega => (base omega, (score omega, skill omega))))
    (candidate : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ)
    (hpositive : 0 < sourceLaw
      (lg21ReportRequiredCandidateSourceNoTakeEvent base skill candidate)) : Prop :=
  let actionLaw :=
    (lg21NormalizedRestriction sourceLaw
      (lg21ReportRequiredCandidateSourceNoTakeEvent base skill candidate)).map
        (fun omega => (base omega, (score omega, skill omega)))
  letI : IsProbabilityMeasure
      (lg21NormalizedRestriction sourceLaw
        (lg21ReportRequiredCandidateSourceNoTakeEvent base skill candidate)) :=
    lg21NormalizedRestriction_isProbability sourceLaw _
      (ne_of_gt hpositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure actionLaw :=
    Measure.isProbabilityMeasure_map hpublic.aemeasurable
  letI : IsFiniteMeasure actionLaw := by
    exact ⟨by simp⟩
  ∀ᵐ publicBase ∂actionLaw.map Prod.fst,
    candidate.noReportPayoff publicBase =
      ∫ latentSkill, latentSkill ∂condDistrib
        (fun scoreSkill : Base × (ℝ × ℝ) => scoreSkill.2.2)
        Prod.fst actionLaw publicBase

/--
The exact source-facing candidate entry needed at a zero-taker endpoint.  The
two PBO fields are literal conditional means on the candidate's selected
positive branches.  The response check is only for members of the candidate's
changed take/report branch and is evaluated before the score is drawn.
-/
def LG21ReportRequiredRecalibratedSourceBranchEntry
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hpublic : Measurable (fun omega => (base omega, (score omega, skill omega))))
    (candidate : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ) : Prop :=
  ∃ htakePositive : 0 < sourceLaw
      (lg21ReportRequiredCandidateSourceTakeEvent base skill candidate),
    ∃ hnoTakePositive : 0 < sourceLaw
      (lg21ReportRequiredCandidateSourceNoTakeEvent base skill candidate),
      LG21ReportRequiredCandidateReportedPBO sourceLaw base score skill hpublic
        candidate htakePositive ∧
        LG21ReportRequiredCandidateNoTakePBO sourceLaw base score skill hpublic
          candidate hnoTakePositive ∧
          PositiveMassBranchMembersBestRespond sourceLaw
            (lg21ReportRequiredCandidateSourceTakeEvent base skill candidate)
            candidate
            (fun C omega =>
              C.noReportPayoff (base omega) <=
                lg21ReportRequiredSequentialTakeExpectedPayoff C
                  (skill omega) (base omega))

/--
An upper-tail selected reporter PBO makes taking a strict pre-score gain for
every type, hence in particular for almost every member of a candidate take
branch.  The displayed posterior is a candidate-side representative; the
separate source certificate below records the a.e. literal PBO identities.
-/
theorem lg21_reportRequired_candidate_takeMembers_bestRespond_of_upperTailPBO
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) (base : Omega -> Base) (skill : Omega -> ℝ)
    (candidate : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ)
    (cutoff : Base -> ℝ) (unselectedPosterior : Base -> ℝ -> Measure ℝ)
    (hnoTake_lt_cutoff : ∀ publicBase,
      candidate.noReportPayoff publicBase < cutoff publicBase)
    (hselectedMassPositive : ∀ publicBase observedScore,
      0 < unselectedPosterior publicBase observedScore
        (Set.Ioi (cutoff publicBase)))
    (hselectedMassFinite : ∀ publicBase observedScore,
      unselectedPosterior publicBase observedScore
        (Set.Ioi (cutoff publicBase)) ≠ ⊤)
    (hselectedSkillIntegrable : ∀ publicBase observedScore,
      Integrable (fun latentSkill : ℝ => latentSkill)
        (lg21NormalizedRestriction
          (unselectedPosterior publicBase observedScore)
          (Set.Ioi (cutoff publicBase))))
    (hreportedPBO : ∀ publicBase observedScore,
      candidate.reportedPayoff publicBase observedScore =
        ∫ latentSkill, latentSkill ∂lg21NormalizedRestriction
          (unselectedPosterior publicBase observedScore)
          (Set.Ioi (cutoff publicBase)))
    (hreportedPBO_integrable : ∀ latentSkill publicBase,
      Integrable (candidate.reportedPayoff publicBase)
        (candidate.testLaw latentSkill publicBase)) :
    PositiveMassBranchMembersBestRespond sourceLaw
      (lg21ReportRequiredCandidateSourceTakeEvent base skill candidate)
      candidate
      (fun C omega =>
        C.noReportPayoff (base omega) <=
          lg21ReportRequiredSequentialTakeExpectedPayoff C
            (skill omega) (base omega)) := by
  rw [PositiveMassBranchMembersBestRespond]
  exact Filter.Eventually.of_forall fun omega => by
    letI : IsProbabilityMeasure (candidate.testLaw (skill omega) (base omega)) :=
      candidate.testLaw_isProbability (skill omega) (base omega)
    change candidate.noReportPayoff (base omega) <=
      ∫ observedScore, candidate.reportedPayoff (base omega) observedScore ∂
        candidate.testLaw (skill omega) (base omega)
    exact le_of_lt
      (lg21_report_required_expected_selected_posterior_gt_no_take
        (candidate.testLaw (skill omega) (base omega))
        (unselectedPosterior (base omega)) (cutoff (base omega))
        (candidate.noReportPayoff (base omega))
        (candidate.reportedPayoff (base omega))
        (hnoTake_lt_cutoff (base omega))
        (hselectedMassPositive (base omega))
        (hselectedMassFinite (base omega))
        (hselectedSkillIntegrable (base omega))
        (hreportedPBO (base omega))
        (hreportedPBO_integrable (skill omega) (base omega)))

/--
Package exact candidate source PBOs with the derived pre-score branch-member
test.  This theorem has no gain-only input and no premise that nonmembers of
the candidate profile already best respond.
-/
theorem lg21_reportRequired_recalibratedSourceBranchEntry_of_upperTailPBO
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hpublic : Measurable (fun omega => (base omega, (score omega, skill omega))))
    (candidate : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ)
    (htakePositive : 0 < sourceLaw
      (lg21ReportRequiredCandidateSourceTakeEvent base skill candidate))
    (hnoTakePositive : 0 < sourceLaw
      (lg21ReportRequiredCandidateSourceNoTakeEvent base skill candidate))
    (hreportedSourcePBO : LG21ReportRequiredCandidateReportedPBO
      sourceLaw base score skill hpublic candidate htakePositive)
    (hnoTakeSourcePBO : LG21ReportRequiredCandidateNoTakePBO
      sourceLaw base score skill hpublic candidate hnoTakePositive)
    (cutoff : Base -> ℝ) (unselectedPosterior : Base -> ℝ -> Measure ℝ)
    (hnoTake_lt_cutoff : ∀ publicBase,
      candidate.noReportPayoff publicBase < cutoff publicBase)
    (hselectedMassPositive : ∀ publicBase observedScore,
      0 < unselectedPosterior publicBase observedScore
        (Set.Ioi (cutoff publicBase)))
    (hselectedMassFinite : ∀ publicBase observedScore,
      unselectedPosterior publicBase observedScore
        (Set.Ioi (cutoff publicBase)) ≠ ⊤)
    (hselectedSkillIntegrable : ∀ publicBase observedScore,
      Integrable (fun latentSkill : ℝ => latentSkill)
        (lg21NormalizedRestriction
          (unselectedPosterior publicBase observedScore)
          (Set.Ioi (cutoff publicBase))))
    (hreportedPBO : ∀ publicBase observedScore,
      candidate.reportedPayoff publicBase observedScore =
        ∫ latentSkill, latentSkill ∂lg21NormalizedRestriction
          (unselectedPosterior publicBase observedScore)
          (Set.Ioi (cutoff publicBase)))
    (hreportedPBO_integrable : ∀ latentSkill publicBase,
      Integrable (candidate.reportedPayoff publicBase)
        (candidate.testLaw latentSkill publicBase)) :
    LG21ReportRequiredRecalibratedSourceBranchEntry
      sourceLaw base score skill hpublic candidate := by
  refine ⟨htakePositive, hnoTakePositive, hreportedSourcePBO,
    hnoTakeSourcePBO, ?_⟩
  exact lg21_reportRequired_candidate_takeMembers_bestRespond_of_upperTailPBO
    sourceLaw base skill candidate cutoff unselectedPosterior
    hnoTake_lt_cutoff hselectedMassPositive hselectedMassFinite
    hselectedSkillIntegrable hreportedPBO hreportedPBO_integrable

end

end LG21TestOptionalPolicies
