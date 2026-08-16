import LG21TestOptionalPolicies.OptionalPartialReporterRecalibratedEntry

/-!
# Candidate no-report branch-response diagnostic for optional LG21 testing

The legacy optional entry carriers certify only members moved to a positive
report branch. This file records the separate score-stage response condition
for members of a candidate's positive no-report branch: an eligible taker who
withholds must not strictly prefer that candidate's own reported value. It is
a diagnostic, not an equilibrium or source-result theorem; in particular it
deliberately does not address the separate pre-score decision whether to take
the test.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set

/--
The score-stage branch-response condition omitted by the legacy
positive-report-entry predicates. Its carrier is semantic: a student has
taken the test under the candidate action, observes a score, and remains on
the candidate's no-report branch. No strategy-function name is used to
identify the condition.
-/
def LG21OptionalCandidateScoreNoReportMembersBestRespond
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) (base : Omega -> Base) (score skill : Omega -> ℝ)
    (candidateTake : ℝ -> Base -> Bool) (candidateReport : Base -> ℝ -> Bool)
    (candidate : LG21OptionalCandidateBranchData ℝ Base ℝ) : Prop :=
  ∀ᵐ omega ∂sourceLaw.restrict
      {omega | candidateTake (skill omega) (base omega) = true ∧
        candidateReport (base omega) (score omega) = false},
    candidate.reportedValue (base omega) (score omega) ≤
      candidate.noReportValue (base omega)

/--
A positive-mass set of candidate takers who remain nonreporters but strictly
prefer the candidate's own reported value refutes score-stage no-report branch
response. This is a missing action-branch test for the legacy optional entry
carriers; it does not assert that every candidate fails the test.
-/
theorem not_lg21OptionalCandidateScoreNoReportMembersBestRespond_of_positive_strict_gain
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) (base : Omega -> Base) (score skill : Omega -> ℝ)
    (candidateTake : ℝ -> Base -> Bool) (candidateReport : Base -> ℝ -> Bool)
    (candidate : LG21OptionalCandidateBranchData ℝ Base ℝ)
    (hpositive : 0 < sourceLaw
      {omega | candidateTake (skill omega) (base omega) = true ∧
        candidateReport (base omega) (score omega) = false})
    (hgain : ∀ᵐ omega ∂sourceLaw.restrict
      {omega | candidateTake (skill omega) (base omega) = true ∧
        candidateReport (base omega) (score omega) = false},
      candidate.noReportValue (base omega) <
        candidate.reportedValue (base omega) (score omega)) :
    ¬ LG21OptionalCandidateScoreNoReportMembersBestRespond
      sourceLaw base score skill candidateTake candidateReport candidate := by
  intro hclosed
  have hfalse : ∀ᵐ omega ∂sourceLaw.restrict
      {omega | candidateTake (skill omega) (base omega) = true ∧
        candidateReport (base omega) (score omega) = false}, False := by
    filter_upwards [hclosed, hgain] with omega hclosed hgain
    exact (not_le_of_gt hgain) hclosed
  have hzeroRestrict : sourceLaw.restrict
      {omega | candidateTake (skill omega) (base omega) = true ∧
        candidateReport (base omega) (score omega) = false} Set.univ = 0 := by
    rw [ae_iff] at hfalse
    simpa using hfalse
  have hzero : sourceLaw
      {omega | candidateTake (skill omega) (base omega) = true ∧
        candidateReport (base omega) (score omega) = false} = 0 := by
    simpa using hzeroRestrict
  exact (ne_of_gt hpositive) hzero

end

end LG21TestOptionalPolicies
