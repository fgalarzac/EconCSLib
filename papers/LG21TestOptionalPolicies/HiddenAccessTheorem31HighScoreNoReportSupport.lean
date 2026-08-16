import LG21TestOptionalPolicies.HiddenAccessTheorem31SourceTimedCandidateEntry
import LG21TestOptionalPolicies.OptionalPartialReporterRecalibratedEntry

/-!
# Literal high-score support for hidden-access nonreporting

These are source-law support facts for the actual access-and-no-report event.
They use only its literal action definition and score coordinate.  In
particular, they neither infer a cutoff for the predecessor action nor turn a
score-local set into a global replacement candidate.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-! ## A literal score-local report-action patch -/

/-- Preserve the predecessor's post-score report decision below `anchor` and
report above it.  The patch depends only on a publicly reported base and the
realized score; it contains no latent-skill or coalition-membership input. -/
def lg21HiddenAccessHighScoreReportPatch
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (anchor : ℝ)
    (currentReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool) :
    (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool :=
  fun publicBase score => if anchor ≤ score then true else currentReport publicBase score

/-- The semantic access/no-report score tail on which the score-local patch
can change a visible action after all taking has been established. -/
def lg21HiddenAccessAccessNoReportHighScoreTail
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (reportDecision : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool)
    (anchor : ℝ) : Set (Bool × (ℝ × (Feature → ℝ))) :=
  lg21HiddenAccessAccessNoReportEvent testFeature reportDecision ∩
    {student | anchor ≤ lg21HiddenAccessStudentScore testFeature student.2}

@[simp] theorem lg21HiddenAccessHighScoreReportPatch_of_le
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) (anchor score : ℝ)
    (currentReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool)
    (publicBase : LG21NonTestFeature Feature testFeature -> ℝ)
    (hscore : anchor ≤ score) :
    lg21HiddenAccessHighScoreReportPatch testFeature anchor currentReport
      publicBase score = true := by
  simp [lg21HiddenAccessHighScoreReportPatch, hscore]

@[simp] theorem lg21HiddenAccessHighScoreReportPatch_of_lt
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) (anchor score : ℝ)
    (currentReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool)
    (publicBase : LG21NonTestFeature Feature testFeature -> ℝ)
    (hscore : score < anchor) :
    lg21HiddenAccessHighScoreReportPatch testFeature anchor currentReport
      publicBase score = currentReport publicBase score := by
  simp [lg21HiddenAccessHighScoreReportPatch, not_le.mpr hscore]

/-- The score-local patch is measurable whenever the predecessor report
decision is measurable. -/
theorem lg21HiddenAccessHighScoreReportPatch_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) (anchor : ℝ)
    (currentReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool)
    (hcurrentReport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      currentReport pair.1 pair.2)) :
    Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      lg21HiddenAccessHighScoreReportPatch testFeature anchor currentReport
        pair.1 pair.2) := by
  unfold lg21HiddenAccessHighScoreReportPatch
  apply Measurable.ite (measurableSet_Ici.preimage measurable_snd)
  · exact measurable_const
  · exact hcurrentReport

/-- Outside the semantic high-score nonreport set, the patch leaves the
post-score action unchanged. -/
theorem lg21HiddenAccessHighScoreReportPatch_eq_current_of_not_highScoreNoReport
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) (anchor score : ℝ)
    (currentReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool)
    (publicBase : LG21NonTestFeature Feature testFeature -> ℝ)
    (hnot : ¬ (currentReport publicBase score = false ∧ anchor ≤ score)) :
    lg21HiddenAccessHighScoreReportPatch testFeature anchor currentReport
      publicBase score = currentReport publicBase score := by
  by_cases hscore : anchor ≤ score
  · have hreport : currentReport publicBase score = true := by
      cases hdecision : currentReport publicBase score with
      | false => exact False.elim (hnot ⟨hdecision, hscore⟩)
      | true => rfl
    simp [lg21HiddenAccessHighScoreReportPatch, hscore, hreport]
  · simp [lg21HiddenAccessHighScoreReportPatch, hscore]

/-- After the pre-score no-take action is null, the score-local patch changes
the final visible action exactly on the literal access/no-report score tail.
This is an a.e. raw-population action identity, not a PBO claim. -/
theorem lg21HiddenAccess_highScorePatch_changedToReportEvent_ae_eq_accessNoReportTail
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (anchor : ℝ)
    (hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      E.activeNoTakeEvent = 0) :
    lg21HiddenAccessCandidateChangedToReportEvent E E.takeDecision
      (lg21HiddenAccessHighScoreReportPatch testFeature anchor E.reportDecision) =ᵐ[
        lg21ContinuousGaussianPopulationLaw M]
      lg21HiddenAccessAccessNoReportHighScoreTail testFeature E.reportDecision anchor := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  have hactiveNull : ∀ᵐ student ∂rawLaw, student ∉ E.activeNoTakeEvent := by
    rw [ae_iff]
    simpa [rawLaw] using hactiveNoTakeZero
  filter_upwards [hactiveNull] with student hnotActive
  apply propext
  rcases student with ⟨access, primitive⟩
  cases access with
  | false =>
      change
        (lg21HiddenAccessOptionalObservedAction testFeature E.takeDecision
          (lg21HiddenAccessHighScoreReportPatch testFeature anchor E.reportDecision)
          (false, primitive) = true ∧
          ¬ lg21HiddenAccessOptionalObservedAction testFeature E.takeDecision
            E.reportDecision (false, primitive) = true) ↔
        ((false = true ∧
          lg21HiddenAccessStudentReport testFeature E.reportDecision primitive = false) ∧
          anchor ≤ lg21HiddenAccessStudentScore testFeature primitive)
      simp [lg21HiddenAccessOptionalObservedAction]
  | true =>
      cases htake : lg21HiddenAccessStudentTake testFeature E.takeDecision primitive with
      | false =>
          exact (hnotActive (by
            simp [LG21HiddenAccessLiteralSourceEquilibriumAE.activeNoTakeEvent,
              htake])).elim
      | true =>
          have htake' : E.takeDecision primitive.1
              (lg21HiddenAccessStudentBase testFeature primitive) = true := by
            simpa [lg21HiddenAccessStudentTake] using htake
          change
            (lg21HiddenAccessOptionalObservedAction testFeature E.takeDecision
              (lg21HiddenAccessHighScoreReportPatch testFeature anchor E.reportDecision)
              (true, primitive) = true ∧
              ¬ lg21HiddenAccessOptionalObservedAction testFeature E.takeDecision
                E.reportDecision (true, primitive) = true) ↔
            ((true = true ∧
              lg21HiddenAccessStudentReport testFeature E.reportDecision primitive = false) ∧
              anchor ≤ lg21HiddenAccessStudentScore testFeature primitive)
          by_cases hscore : anchor ≤ lg21HiddenAccessStudentScore testFeature primitive
          · cases hreport : E.reportDecision
              (lg21HiddenAccessStudentBase testFeature primitive)
              (lg21HiddenAccessStudentScore testFeature primitive) <;>
              simp [lg21HiddenAccessOptionalObservedAction,
                lg21HiddenAccessStudentTake, lg21HiddenAccessStudentReport,
                lg21HiddenAccessHighScoreReportPatch,
                htake', hscore, hreport]
          · cases hreport : E.reportDecision
              (lg21HiddenAccessStudentBase testFeature primitive)
              (lg21HiddenAccessStudentScore testFeature primitive) <;>
              simp [lg21HiddenAccessOptionalObservedAction,
                lg21HiddenAccessStudentTake, lg21HiddenAccessStudentReport,
                lg21HiddenAccessHighScoreReportPatch,
                htake', hscore, hreport]

/-- The preceding a.e. action identity yields equality of literal source
mass. -/
theorem lg21HiddenAccess_highScorePatch_changedToReport_mass_eq_accessNoReportTail
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (anchor : ℝ)
    (hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      E.activeNoTakeEvent = 0) :
    lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessCandidateChangedToReportEvent E E.takeDecision
        (lg21HiddenAccessHighScoreReportPatch testFeature anchor E.reportDecision)) =
      lg21ContinuousGaussianPopulationLaw M
        (lg21HiddenAccessAccessNoReportHighScoreTail
          testFeature E.reportDecision anchor) := by
  exact measure_congr
    (lg21HiddenAccess_highScorePatch_changedToReportEvent_ae_eq_accessNoReportTail
      E anchor hactiveNoTakeZero)

/-- A positive literal access/no-report score tail gives the score-local
patch a positive changed visible-action branch after all taking. -/
theorem lg21HiddenAccess_highScorePatch_changedToReport_positive_of_accessNoReportTail
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (anchor : ℝ)
    (hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      E.activeNoTakeEvent = 0)
    (htailPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessAccessNoReportHighScoreTail
        testFeature E.reportDecision anchor)) :
    0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessCandidateChangedToReportEvent E E.takeDecision
        (lg21HiddenAccessHighScoreReportPatch testFeature anchor E.reportDecision)) := by
  rw [lg21HiddenAccess_highScorePatch_changedToReport_mass_eq_accessNoReportTail
    E anchor hactiveNoTakeZero]
  exact htailPositive

/-- The score-local patch's visible report branch is positive whenever its
changed-to-report branch is positive. -/
theorem lg21HiddenAccess_highScorePatch_report_positive_of_accessNoReportTail
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (anchor : ℝ)
    (hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      E.activeNoTakeEvent = 0)
    (htailPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessAccessNoReportHighScoreTail
        testFeature E.reportDecision anchor)) :
    0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessRawCandidateReportEvent testFeature E.takeDecision
        (lg21HiddenAccessHighScoreReportPatch testFeature anchor E.reportDecision)) := by
  apply lt_of_lt_of_le
    (lg21HiddenAccess_highScorePatch_changedToReport_positive_of_accessNoReportTail
      E anchor hactiveNoTakeZero htailPositive)
  apply measure_mono
  intro student hchanged
  exact hchanged.1

/-- The score-local patch retains a positive literal no-report branch whenever
the source has positive no-access mass. This is the raw `X = 0` law, so the
no-access component remains in scope for a later PBO calculation. -/
theorem lg21HiddenAccess_highScorePatch_noReport_positive_of_noAccess
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (testFeature : Feature)
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (anchor : ℝ)
    (hnoAccess : 0 < M.accessLaw {false}) :
    0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessRawCandidateNoReportEvent testFeature E.takeDecision
        (lg21HiddenAccessHighScoreReportPatch testFeature anchor E.reportDecision)) := by
  exact lg21HiddenAccessRawCandidate_noReport_positive_of_noAccess M testFeature
    E.takeDecision
    (lg21HiddenAccessHighScoreReportPatch testFeature anchor E.reportDecision)
    hnoAccess

/-- A positive-mass literal access/no-report population has a positive-mass
tail above some finite score.  This is a semantic statement about the raw
action event, not a property inferred from the name of the report function. -/
theorem lg21HiddenAccess_exists_highScoreTail_of_positive_accessNoReport
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (reportDecision : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool)
    (hpositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessAccessNoReportEvent testFeature reportDecision)) :
    ∃ anchor : ℝ, 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessAccessNoReportHighScoreTail
        testFeature reportDecision anchor) := by
  simpa [lg21HiddenAccessAccessNoReportHighScoreTail] using
    (lg21_exists_highScoreTail_of_positive_mass
    (lg21ContinuousGaussianPopulationLaw M)
    (fun student : Bool × (ℝ × (Feature -> ℝ)) =>
      lg21HiddenAccessStudentScore testFeature student.2)
    (lg21HiddenAccessAccessNoReportEvent testFeature reportDecision) hpositive)

/-- A source-level all-take-to-support bridge.  If literal access students
withhold on positive mass, then some finite high-score patch changes a
positive visible-action mass while preserving the predecessor's `Y` action.
No PBO or whole-candidate equilibrium is asserted here. -/
theorem lg21HiddenAccess_exists_positive_highScorePatchChange_of_positive_accessNoReport
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      E.activeNoTakeEvent = 0)
    (hpositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessAccessNoReportEvent testFeature E.reportDecision)) :
    ∃ anchor : ℝ, 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessCandidateChangedToReportEvent E E.takeDecision
        (lg21HiddenAccessHighScoreReportPatch testFeature anchor E.reportDecision)) := by
  rcases lg21HiddenAccess_exists_highScoreTail_of_positive_accessNoReport
      M testFeature E.reportDecision hpositive with ⟨anchor, htailPositive⟩
  exact ⟨anchor,
    lg21HiddenAccess_highScorePatch_changedToReport_positive_of_accessNoReportTail
      E anchor hactiveNoTakeZero htailPositive⟩

/-- If every finite high-score tail of the literal access/no-report event is
null, then the whole event is null.  A future score-local candidate argument
may supply the tail premise; this theorem does not pretend that base-local
candidate stability supplies it by itself. -/
theorem lg21HiddenAccess_accessNoReport_measure_zero_of_all_highScoreTails_zero
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (reportDecision : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool)
    (htailZero : ∀ anchor : ℝ,
      lg21ContinuousGaussianPopulationLaw M
        (lg21HiddenAccessAccessNoReportHighScoreTail
          testFeature reportDecision anchor) = 0) :
    lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessAccessNoReportEvent testFeature reportDecision) = 0 := by
  by_contra hnonzero
  have hpositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessAccessNoReportEvent testFeature reportDecision) :=
    pos_iff_ne_zero.mpr hnonzero
  rcases lg21HiddenAccess_exists_highScoreTail_of_positive_accessNoReport
      M testFeature reportDecision hpositive with
    ⟨anchor, htailPositive⟩
  exact (ne_of_gt htailPositive) (htailZero anchor)

end

end LG21TestOptionalPolicies
