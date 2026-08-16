import LG21TestOptionalPolicies.HiddenAccessTheorem31SourceTimedCandidateEntry

/-!
# Score-local patch response bridge for LG21 Theorem 3.1

This module isolates the deterministic best-response part of the local
score-patch argument.  The patch retains incumbent reports and adds only
scores with a strict candidate gain.  If recalibrating the candidate's
no-report branch weakly lowers its value, then incumbent reporters and the
newly promoted scores both weakly prefer reporting.

The theorem is intentionally agnostic about how the PBO identities and the
no-report mean comparison are established.  Those are measure-theoretic
source-law obligations, not facts inferred from a function name or a cutoff
representation.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set

/-- Preserve every incumbent report and add the scores selected by a public
Boolean promotion rule. -/
def lg21HiddenAccessScoreLocalReportPatch
    {Base : Type*}
    (currentReport promote : Base -> ℝ -> Bool) : Base -> ℝ -> Bool :=
  fun publicBase score => currentReport publicBase score || promote publicBase score

@[simp] theorem lg21HiddenAccessScoreLocalReportPatch_eq_true_iff
    {Base : Type*}
    (currentReport promote : Base -> ℝ -> Bool)
    (publicBase : Base) (score : ℝ) :
    lg21HiddenAccessScoreLocalReportPatch currentReport promote publicBase score = true ↔
      currentReport publicBase score = true ∨ promote publicBase score = true := by
  simp [lg21HiddenAccessScoreLocalReportPatch]

@[simp] theorem lg21HiddenAccessScoreLocalReportPatch_preserves_report
    {Base : Type*}
    (currentReport promote : Base -> ℝ -> Bool)
    (publicBase : Base) (score : ℝ)
    (hcurrent : currentReport publicBase score = true) :
    lg21HiddenAccessScoreLocalReportPatch currentReport promote publicBase score = true := by
  simp [lg21HiddenAccessScoreLocalReportPatch, hcurrent]

@[simp] theorem lg21HiddenAccessScoreLocalReportPatch_promotes
    {Base : Type*}
    (currentReport promote : Base -> ℝ -> Bool)
    (publicBase : Base) (score : ℝ)
    (hpromote : promote publicBase score = true) :
    lg21HiddenAccessScoreLocalReportPatch currentReport promote publicBase score = true := by
  simp [lg21HiddenAccessScoreLocalReportPatch, hpromote]

/-- A candidate report branch is a.e. best responding when its members are
either preserved incumbent reporters or newly promoted scores with a strict
gain.  The hypotheses are semantic payoff comparisons on the attained branch;
they do not assume a cutoff form for either report action. -/
theorem lg21_positiveMassBranchMembersBestRespond_of_preserved_or_improved
    {Omega Base : Type*} [MeasurableSpace Omega]
    (sourceLaw : Measure Omega) (reportBranch : Set Omega)
    (base : Omega -> Base) (score : Omega -> ℝ)
    (currentReport : Base -> ℝ -> Bool)
    (incumbentNoReport : Base -> ℝ)
    (incumbentReported : Base -> ℝ -> ℝ)
    (candidate : LG21OptionalCandidateBranchData ℝ Base ℝ)
    (hcandidateNoReport_le : ∀ᵐ omega ∂sourceLaw.restrict reportBranch,
      candidate.noReportValue (base omega) ≤ incumbentNoReport (base omega))
    (hincumbentBestResponse : ∀ᵐ omega ∂sourceLaw.restrict reportBranch,
      currentReport (base omega) (score omega) = true ->
        incumbentNoReport (base omega) ≤
          incumbentReported (base omega) (score omega))
    (hmemberClassifies : ∀ᵐ omega ∂sourceLaw.restrict reportBranch,
      (currentReport (base omega) (score omega) = true ∧
        candidate.reportedValue (base omega) (score omega) =
          incumbentReported (base omega) (score omega)) ∨
      incumbentNoReport (base omega) <
        candidate.reportedValue (base omega) (score omega)) :
    PositiveMassBranchMembersBestRespond sourceLaw reportBranch candidate
      (fun P omega =>
        P.noReportValue (base omega) ≤ P.reportedValue (base omega) (score omega)) := by
  rw [PositiveMassBranchMembersBestRespond]
  filter_upwards [hcandidateNoReport_le, hincumbentBestResponse, hmemberClassifies]
    with omega hcandidateNoReport hincumbentBR hclassifies
  rcases hclassifies with hincumbent | hpromoted
  · calc
      candidate.noReportValue (base omega) ≤ incumbentNoReport (base omega) :=
        hcandidateNoReport
      _ ≤ incumbentReported (base omega) (score omega) :=
        hincumbentBR hincumbent.1
      _ = candidate.reportedValue (base omega) (score omega) := hincumbent.2.symm
  · exact hcandidateNoReport.trans (le_of_lt hpromoted)

end

end LG21TestOptionalPolicies
