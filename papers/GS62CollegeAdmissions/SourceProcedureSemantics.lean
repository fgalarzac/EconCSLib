import GS62CollegeAdmissions.CollegeBatchedProcedure

/-!
# Legacy global-permission helper for the cloned-seat runner

This auxiliary module predates the direct Section 4 runner.  It shows that the
cloned-seat schedule respects a *global* one-way permission hypothesis.  That
hypothesis is stronger than the source's pairwise application filter and is
not a paper-domain assumption or part of `PaperInterface.lean`.

The source-facing rule is the mutual per-pair predicate in
`ExactCollegeBatchedProcedure.sourceEligible`: both the applicant and college
list the pair.  Keep the lemmas below only as support for the legacy schedule.
-/

namespace GS62CollegeAdmissions

open EconCSLib.Matching

namespace SourceProcedureSemantics

variable {Applicants Colleges : Type*}
  [Fintype Applicants] [Fintype Colleges]
  [DecidableEq Applicants] [DecidableEq Colleges]

/--
Auxiliary global condition used by this legacy proof: every applicant-positive
pair is also college-positive.  This is deliberately not presented as the
source's general preference-domain condition.
-/
def gs62PermittedCollegeApplications
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ) : Prop :=
  ∀ a c, 0 < val_applicant a c → 0 < val_college c a

/--
Every best remaining cloned seat of an active applicant belongs to a college
that permits that applicant under the auxiliary global condition.
-/
theorem bestRemainingWoman_underlying_college_permitted
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (happNoZero : ∀ a c, val_applicant a c ≠ 0)
    (hpermitted : gs62PermittedCollegeApplications val_applicant val_college)
    (s : DAState Applicants (ManyToOneOptimality.Seat quota))
    (a : Applicants)
    (best : ManyToOneOptimality.Seat quota)
    (hbest : BestRemainingWoman
      (ManyToOneOptimality.refinedApplicantSeatValue
        quota val_applicant happNoZero) s a best) :
    0 < val_college best.1 a := by
  have hspec := ManyToOneOptimality.refinedApplicantSeatValue_spec
    quota val_applicant happNoZero
  have hrefinedPositive : 0 <
      ManyToOneOptimality.refinedApplicantSeatValue
        quota val_applicant happNoZero a best :=
    lt_of_le_of_ne hbest.2.1 (hspec.nonzero a best).symm
  have happlicantPositive : 0 < val_applicant a best.1 :=
    (hspec.positive_iff a best).1 hrefinedPositive
  exact hpermitted a best.1 happlicantPositive

/--
The legacy college application block has one permitted target college:
it repeats the applicant once for every remaining cloned seat of that college,
and that college positively values the applicant.  Thus the cloned-seat
batching representation does not introduce applications forbidden by the
auxiliary global condition.
-/
theorem collegeApplicationBlock_shape_of_active_permitted
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (happNoZero : ∀ a c, val_applicant a c ≠ 0)
    (hpermitted : gs62PermittedCollegeApplications val_applicant val_college)
    (s : DAState Applicants (ManyToOneOptimality.Seat quota))
    (a : Applicants)
    (hactive : IsActiveMan
      (ManyToOneOptimality.refinedApplicantSeatValue
        quota val_applicant happNoZero) s a) :
    ∃ best : ManyToOneOptimality.Seat quota,
      BestRemainingWoman
          (ManyToOneOptimality.refinedApplicantSeatValue
            quota val_applicant happNoZero) s a best ∧
        0 < val_college best.1 a ∧
        CollegeBatchedProcedure.collegeApplicationBlock
            quota val_applicant happNoZero s a =
          List.replicate
            ((s.m_proposals a).filter fun seat => seat.1 = best.1).card a ∧
        0 < ((s.m_proposals a).filter fun seat => seat.1 = best.1).card := by
  rcases CollegeBatchedProcedure.collegeApplicationBlock_shape_of_active
      quota val_applicant happNoZero s a hactive with
    ⟨best, hbest, hshape, hcard⟩
  refine ⟨best, hbest, ?_, hshape, hcard⟩
  exact bestRemainingWoman_underlying_college_permitted
    quota val_applicant val_college happNoZero hpermitted s a best hbest

end SourceProcedureSemantics
end GS62CollegeAdmissions
