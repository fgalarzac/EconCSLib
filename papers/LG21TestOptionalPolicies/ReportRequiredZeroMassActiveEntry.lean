import LG21TestOptionalPolicies.PositiveMassDeviation

/-!
# Positive-mass active entry at the report-required zero-taker endpoint

The source says that the school knows the decision functions and that its PBO
follows them.  At a null report branch, an arbitrary value of a conditional
distribution is not an operational interpretation of those sentences.  This
module instead evaluates a *positive-mass candidate action* using the PBOs
induced by that candidate's actual action events.

The result below is deliberately semantic rather than API-shaped.  It does
not inspect a function name, assume that an equilibrium action rule is a
cutoff, or assign a payoff to a null branch.  Given any candidate whose
remaining no-take branch lies below a boundary and whose entering branch lies
at or above it, literal conditional means make every entering type strictly
prefer taking.  The tail corollary then supplies the positive-mass active
entry witness needed to rule out an all-no-take profile under the
source-faithful candidate-PBO interpretation.

The source-facing Gaussian bridge remains responsible for constructing the
explicit selected posterior kernel, proving its positive selected mass and
integrability, and identifying the paper PBO with the displayed conditional
means.  Those obligations are intentionally visible in the theorem inputs.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set

/-! ## Semantic active-entry certificates -/

/--
A positive-mass report-required entry certificate.  The strict comparison is
made against the **candidate** no-take estimate and candidate reported-score
estimate.  Thus this is not a unilateral comparison against an arbitrary
value supplied at the predecessor's null report branch.
-/
def LG21ReportRequiredPositiveMassEntry
    {Test : Type*} [MeasurableSpace Test]
    (skillLaw : Measure ℝ) (entrant : Set ℝ)
    (testLaw : ℝ → Measure Test)
    (reportedEstimate : Test → ℝ) (noTakeEstimate : ℝ) : Prop :=
  0 < skillLaw entrant ∧
    ∀ skill, skill ∈ entrant →
      noTakeEstimate < ∫ test, reportedEstimate test ∂testLaw skill

/--
The semantic statement that an all-no-take profile admits an active
positive-mass report-required entry.  It is intentionally a witness property:
the eventual source-facing equilibrium bridge must still show that the
candidate action is feasible and connect this certificate to Definition 1's
candidate-profile best-response predicate.
-/
def LG21ReportRequiredAllNoTakeHasActiveEntry
    {Test : Type*} [MeasurableSpace Test]
    (skillLaw : Measure ℝ) (testLaw : ℝ → Measure Test)
    (reportedEstimate : Test → ℝ) (noTakeEstimate : ℝ) : Prop :=
  ∃ entrant,
    LG21ReportRequiredPositiveMassEntry skillLaw entrant testLaw
      reportedEstimate noTakeEstimate

/-! ## A generic high-tail candidate -/

/--
For a positive-mass candidate split, literal branch conditional means force a
strict taking incentive for every member of a high entrant branch.

`remaining` and `entrant` are arbitrary measurable action events.  Their
order relative to `boundary` is a property of the **constructed candidate**,
not an assumed representation of an equilibrium.  The posterior hypotheses
are stated as measures rather than as a field named "PBO": each reported
estimate must equal the conditional skill mean of the posterior selected by
the candidate entrant event.
-/
theorem lg21_reportRequired_positiveMassEntry_of_candidateBranchMeans
    {Test : Type*} [MeasurableSpace Test]
    (skillLaw : Measure ℝ) [IsProbabilityMeasure skillLaw]
    [IsFiniteMeasure skillLaw]
    (remaining entrant : Set ℝ) (boundary : ℝ)
    (hremainingMeasurable : MeasurableSet remaining)
    (hentrantMeasurable : MeasurableSet entrant)
    (hremainingPositive : 0 < skillLaw remaining)
    (hentrantPositive : 0 < skillLaw entrant)
    (hremainingBelow : ∀ skill ∈ remaining, skill < boundary)
    (hentrantAbove : ∀ skill ∈ entrant, boundary ≤ skill)
    (noTakeEstimate : ℝ)
    (hnoTakeEstimate : noTakeEstimate =
      ∫ skill, skill ∂lg21NormalizedRestriction skillLaw remaining)
    (hremainingIntegrable :
      Integrable (fun skill : ℝ => skill)
        (lg21NormalizedRestriction skillLaw remaining))
    (rawScorePosterior : Test → Measure ℝ)
    (hrawScorePosteriorFinite : ∀ test, IsFiniteMeasure (rawScorePosterior test))
    (hselectedMassPositive : ∀ test,
      0 < rawScorePosterior test entrant)
    (hselectedIntegrable : ∀ test,
      Integrable (fun skill : ℝ => skill)
        (lg21NormalizedRestriction (rawScorePosterior test) entrant))
    (reportedEstimate : Test → ℝ)
    (hreportedEstimate : ∀ test, reportedEstimate test =
      ∫ skill, skill ∂lg21NormalizedRestriction
        (rawScorePosterior test) entrant)
    (testLaw : ℝ → Measure Test)
    (htestLawProbability : ∀ skill, IsProbabilityMeasure (testLaw skill))
    (hreportedIntegrable : ∀ skill,
      Integrable reportedEstimate (testLaw skill)) :
    LG21ReportRequiredPositiveMassEntry skillLaw entrant testLaw
      reportedEstimate noTakeEstimate := by
  have hnoTakeBelowBoundary : noTakeEstimate < boundary := by
    rw [hnoTakeEstimate]
    exact lg21NormalizedRestriction_mean_lt_upper
      skillLaw remaining (fun skill : ℝ => skill) boundary
      hremainingMeasurable hremainingPositive hremainingIntegrable
      hremainingBelow
  have hreportedAboveNoTake : ∀ test,
      noTakeEstimate < reportedEstimate test := by
    intro test
    letI : IsFiniteMeasure (rawScorePosterior test) :=
      hrawScorePosteriorFinite test
    rw [hreportedEstimate test]
    exact lg21NormalizedRestriction_mean_gt_lower
      (rawScorePosterior test) entrant (fun skill : ℝ => skill)
      noTakeEstimate hentrantMeasurable (hselectedMassPositive test)
      (hselectedIntegrable test)
      (fun selectedSkill hselectedSkill =>
        lt_of_lt_of_le hnoTakeBelowBoundary
          (hentrantAbove selectedSkill hselectedSkill))
  refine ⟨hentrantPositive, ?_⟩
  intro skill _hskill
  letI : IsProbabilityMeasure (testLaw skill) := htestLawProbability skill
  have hstrictIntegral := lg21_integral_lt_integral_of_ae_lt_probability
    (testLaw skill)
    (integrable_const noTakeEstimate)
    (hreportedIntegrable skill)
    (Filter.Eventually.of_forall (hreportedAboveNoTake))
  simpa using hstrictIntegral

/-! ## The all-no-take endpoint -/

/--
An upper-tail candidate supplies a positive-mass active entry at the
all-no-take endpoint whenever both of the candidate's action branches have
positive mass and are calibrated to their literal conditional means.

This theorem does **not** assume that a supplied equilibrium has a threshold
form.  `boundary` only describes the explicit candidate deviation used to
test the zero-taker endpoint.  In the LG21 Gaussian source law, positivity of
both tails, selected-posterior positivity, and integrability are separate
source-law obligations.
-/
theorem lg21_reportRequired_allNoTake_has_positiveMass_upperTailEntry
    {Test : Type*} [MeasurableSpace Test]
    (skillLaw : Measure ℝ) [IsProbabilityMeasure skillLaw]
    [IsFiniteMeasure skillLaw]
    (boundary : ℝ)
    (hbelowPositive : 0 < skillLaw (Set.Iio boundary))
    (habovePositive : 0 < skillLaw (Set.Ici boundary))
    (noTakeEstimate : ℝ)
    (hnoTakeEstimate : noTakeEstimate =
      ∫ skill, skill ∂lg21NormalizedRestriction skillLaw (Set.Iio boundary))
    (hbelowIntegrable :
      Integrable (fun skill : ℝ => skill)
        (lg21NormalizedRestriction skillLaw (Set.Iio boundary)))
    (rawScorePosterior : Test → Measure ℝ)
    (hrawScorePosteriorFinite : ∀ test, IsFiniteMeasure (rawScorePosterior test))
    (hselectedMassPositive : ∀ test,
      0 < rawScorePosterior test (Set.Ici boundary))
    (hselectedIntegrable : ∀ test,
      Integrable (fun skill : ℝ => skill)
        (lg21NormalizedRestriction (rawScorePosterior test) (Set.Ici boundary)))
    (reportedEstimate : Test → ℝ)
    (hreportedEstimate : ∀ test, reportedEstimate test =
      ∫ skill, skill ∂lg21NormalizedRestriction
        (rawScorePosterior test) (Set.Ici boundary))
    (testLaw : ℝ → Measure Test)
    (htestLawProbability : ∀ skill, IsProbabilityMeasure (testLaw skill))
    (hreportedIntegrable : ∀ skill,
      Integrable reportedEstimate (testLaw skill)) :
    LG21ReportRequiredAllNoTakeHasActiveEntry skillLaw testLaw
      reportedEstimate noTakeEstimate := by
  refine ⟨Set.Ici boundary, ?_⟩
  exact lg21_reportRequired_positiveMassEntry_of_candidateBranchMeans
    skillLaw (Set.Iio boundary) (Set.Ici boundary) boundary
    measurableSet_Iio measurableSet_Ici hbelowPositive habovePositive
    (fun skill hskill => hskill)
    (fun skill hskill => hskill)
    noTakeEstimate hnoTakeEstimate hbelowIntegrable
    rawScorePosterior hrawScorePosteriorFinite hselectedMassPositive
    hselectedIntegrable reportedEstimate hreportedEstimate
    testLaw htestLawProbability hreportedIntegrable

end

end LG21TestOptionalPolicies
