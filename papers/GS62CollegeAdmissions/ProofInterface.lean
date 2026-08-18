import GS62CollegeAdmissions.PaperInterface

/-!
# Proof endpoints: Gale--Shapley 1962

This module holds the compiled endpoint for each source-facing `Spec` in
`PaperInterface.lean`.  It is intentionally separate from the paper review
surface: reviewers compare the raw source excerpts only with the corresponding
expanded `Spec`; these theorems supply proof evidence for those specifications.
-/

namespace GS62CollegeAdmissions
namespace PaperInterface

theorem unstableMarriage_iff_source_definition :
    unstableMarriage_iff_source_definitionSpec := by
  intro M W val_m val_w mu
  rfl

theorem unstableCollegeAssignment_iff_source_definition :
    unstableCollegeAssignment_iff_source_definitionSpec := by
  intro Applicants Colleges val_applicant val_college mu
  rfl

theorem literalApplicantOptimalCollegeAssignment_iff_source_definition :
    literalApplicantOptimalCollegeAssignment_iff_source_definitionSpec := by
  intro Applicants Colleges val_applicant val_college mu
  rfl

theorem theorem1_stable_marriage_exists :
    theorem1_stable_marriage_existsSpec := by
  intro M W _ _ _ _ val_m val_w hcard hmen hwomen hmenacceptable hwomenacceptable
  have hdomain : strictMarriageDomain val_m val_w :=
    ⟨hmen, hwomen, hmenacceptable, hwomenacceptable⟩
  rcases paper_gs62_theorem1_stable_marriage_exists
      val_m val_w hcard hdomain with ⟨mu, hstable, hcomplete⟩
  refine ⟨mu, ?_, hcomplete⟩
  intro hunstable
  rcases hunstable with ⟨hcomplete', hblocking⟩
  rcases hblocking with ⟨m0, w0, hcomparisons⟩
  exact hstable.2.2 m0 w0 hcomparisons.1 hcomparisons.2

theorem theorem2_applicant_optimality :
    theorem2_applicant_optimalitySpec := by
  intro Applicants Colleges _ _ _ _ quota val_applicant val_college
    happlicant_strict hcollege_strict
  let hdomain : gs_strict_college_admissions_domain val_applicant val_college :=
    ⟨happlicant_strict, hcollege_strict⟩
  constructor
  · exact
      ⟨ExactCollegeBatchedProcedure.sourceWaitingListFinalState quota
          val_applicant val_college hcollege_strict.1,
        ExactCollegeBatchedProcedure.sourceWaitingListFinalState_reachable
          quota val_applicant val_college hcollege_strict.1,
        ExactCollegeBatchedProcedure.sourceWaitingListFinalState_terminated
          quota val_applicant val_college hcollege_strict.1⟩
  · intro s hreachable hterminal
    have hoptimal :=
      ExactCollegeBatchedProcedure.paper_gs62_source_reachable_terminal_assignment_applicant_optimal
        quota val_applicant val_college hdomain s hreachable hterminal
    simpa [applicantOptimalCollegeAssignment,
      gs_applicant_optimal_college_assignment,
      gs_stable_college_assignment,
      EconCSLib.Matching.ManyToOne.IsStable,
      EconCSLib.Matching.ManyToOneAssignment.RespectsQuota,
      EconCSLib.Matching.ManyToOne.CollegeWouldAccept] using hoptimal

end PaperInterface
end GS62CollegeAdmissions
