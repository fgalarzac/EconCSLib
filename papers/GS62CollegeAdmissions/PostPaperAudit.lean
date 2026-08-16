import GS62CollegeAdmissions.PaperInterface

/-!
# Post-paper audit: Gale--Shapley 1962

Lean-side endpoint ledger for Gale and Shapley's *College Admissions and the
Stability of Marriage*.

Every endpoint below delegates to the proved paper route imported by
`PaperInterface.lean`. This file is an auxiliary compile receipt, not the
paper's review surface; the review surface is `PaperInterface.lean` itself.

The pinned ignored scan is `source.pdf`, SHA-256
`953a8123e8120a86b17ae3de92cb51abb5aed420fe11b97fe2a666a8e637d09b`.
All printed pages 9--15 were inspected directly.  Normal coverage consists of
the two displayed college definitions, the prose marriage-instability
definition, and Theorems 1 and 2.  The wrappers below additionally compile a
few procedure-support endpoints without promoting examples or unnumbered
prose consequences into normal named-theory targets.
-/

namespace GS62CollegeAdmissions
namespace PostPaperAudit

open EconCSLib.Matching
open PaperInterface

/-- Audit endpoint for Theorem 1. -/
theorem theorem1
    {M W : Type*} [Fintype M] [Fintype W]
    [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : strictMarriageDomain val_m val_w) :
    ∃ mu : Assignment M W,
      ¬ unstableMarriage val_m val_w mu ∧ completeMarriage mu :=
  theorem1_stable_marriage_exists val_m val_w hcard hdomain

/-- Audit endpoint for the printed batched-stage bound. -/
theorem exact_marriage_stage_bound
    {A : Type*} [Fintype A] [DecidableEq A]
    (val_m : A → A → ℝ) (val_w : A → A → ℝ)
    (hnonempty : 0 < Fintype.card A)
    (hdomain : strictMarriageDomain val_m val_w) :
    ¬ ∃ m, IsActiveMan val_m
      (gsStateAfterBatches val_m val_w
        (gsBatchedStageBound (Fintype.card A))) m :=
  marriage_batched_stage_bound val_m val_w hnonempty hdomain

/-- Audit endpoint for the source top-`q` waiting-list simulation. -/
theorem college_waiting_list_bridge
    {Applicants Colleges : Type*}
    [Fintype Applicants] [Fintype Colleges]
    [DecidableEq Applicants] [DecidableEq Colleges]
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hdomain : strictCollegeAdmissionsDomain val_applicant val_college) :
    ExactCollegeBatchedProcedure.sourceWaitingListFinalAssignment
        quota val_applicant val_college hdomain.2.1 =
      ManyToOneOptimality.refinedDeferredAcceptanceManyToOne
        quota val_applicant val_college hdomain.1.2 :=
  college_waiting_list_agrees_with_applicant_da
    quota val_applicant val_college hdomain

/-- Audit endpoint for arbitrary-quota Theorem 2. -/
theorem theorem2
    {Applicants Colleges : Type*}
    [Fintype Applicants] [Fintype Colleges]
    [DecidableEq Applicants] [DecidableEq Colleges]
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hdomain : strictCollegeAdmissionsDomain val_applicant val_college) :
    applicantOptimalCollegeAssignment quota val_applicant val_college
      (ExactCollegeBatchedProcedure.sourceWaitingListFinalAssignment
        quota val_applicant val_college hdomain.2.1) :=
  ExactCollegeBatchedProcedure.paper_gs62_source_waiting_list_assignment_applicant_optimal
    quota val_applicant val_college hdomain

/--
Audit endpoint for the inverted unique college-optimal outcome under the
explicit responsive cloned-seat roster convention.
-/
theorem inverted_responsive_college_optimal
    {Applicants Colleges : Type*}
    [Fintype Applicants] [Fintype Colleges]
    [DecidableEq Applicants] [DecidableEq Colleges]
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hdomain : strictCollegeAdmissionsDomain val_applicant val_college) :
    let mu := ManyToOneOptimality.collegeProposingManyToOne
      quota val_applicant val_college hdomain.1.2
    responsiveCollegeOptimalAssignment quota val_applicant val_college mu ∧
      ∀ nu, responsiveCollegeOptimalAssignment quota val_applicant
        val_college nu → nu = mu :=
  inverted_college_proposing_unique_responsive_college_optimal
    quota val_applicant val_college hdomain

end PostPaperAudit
end GS62CollegeAdmissions
