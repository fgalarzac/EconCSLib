import GS62CollegeAdmissions.SourceModel

/-!
# Paper Interface: Gale--Shapley 1962

This is the complete human semantic-review surface for Gale and Shapley's
*College Admissions and the Stability of Marriage*.  It intentionally contains
one transparent `Spec : Prop` declaration per reviewed source claim and no
source-model wrappers, operational helper declarations, or proof endpoints.
Those live in `SourceModel.lean` and `ProofInterface.lean` respectively.

The normal source surface consists of the Section 3 marriage-instability
definition, the two printed college definitions on page 10, and Theorems 1--2.
For Theorem 2, ``stable assignment'' is read in the completed operational sense
used by Sections 4--5: a quota-feasible, individually rational assignment with
no applicant-college blocking pair, including an acceptable vacant seat.  The
page-10 replacement-pair display remains a separate literal definition below.
-/

namespace GS62CollegeAdmissions
namespace PaperInterface

open EconCSLib.Matching

/-- The Section 3 definition of an unstable complete marriage. -/
def unstableMarriage_iff_source_definitionSpec : Prop :=
  ∀ {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W),
    unstableMarriage val_m val_w mu ↔
      ((∀ m, ∃ w, mu.m_match m = some w) ∧
        ∀ w, ∃ m, mu.w_match w = some m) ∧
        ∃ m w,
          valM val_m m (mu.m_match m) < val_m m w ∧
            valW val_w w (mu.w_match w) < val_w w m

/-- The literal page-10 replacement-pair definition of instability. -/
def unstableCollegeAssignment_iff_source_definitionSpec : Prop :=
  ∀ {Applicants Colleges : Type*}
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : ManyToOneAssignment Applicants Colleges),
    unstableCollegeAssignment val_applicant val_college mu ↔
      ∃ alpha beta A B,
        mu.app_match alpha = some A ∧
          mu.app_match beta = some B ∧
            val_applicant beta B < val_applicant beta A ∧
              val_college A alpha < val_college A beta

/-- The literal page-10 definition of applicant optimality. -/
def literalApplicantOptimalCollegeAssignment_iff_source_definitionSpec : Prop :=
  ∀ {Applicants Colleges : Type*}
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : ManyToOneAssignment Applicants Colleges),
    literalApplicantOptimalCollegeAssignment val_applicant val_college mu ↔
      (¬ ∃ alpha beta A B,
        mu.app_match alpha = some A ∧
          mu.app_match beta = some B ∧
            val_applicant beta B < val_applicant beta A ∧
              val_college A alpha < val_college A beta) ∧
        ∀ (nu : ManyToOneAssignment Applicants Colleges),
          (¬ ∃ alpha beta A B,
            nu.app_match alpha = some A ∧
              nu.app_match beta = some B ∧
                val_applicant beta B < val_applicant beta A ∧
                  val_college A alpha < val_college A beta) →
            ∀ a,
              (match nu.app_match a with
                | none => 0
                | some c => val_applicant a c) ≤
                match mu.app_match a with
                  | none => 0
                  | some c => val_applicant a c

/-- Theorem 1: stable marriage exists in the finite strict complete domain. -/
def theorem1_stable_marriage_existsSpec : Prop :=
  ∀ {M W : Type*} [Fintype M] [Fintype W]
    [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ),
    Fintype.card M = Fintype.card W →
      (∀ m w w', val_m m w = val_m m w' → w = w') →
      (∀ w m m', val_w w m = val_w w m' → m = m') →
      (∀ m w, 0 < val_m m w) →
      (∀ w m, 0 < val_w w m) →
      ∃ mu : Assignment M W,
        (¬ (((∀ m, ∃ w, mu.m_match m = some w) ∧
          ∀ w, ∃ m, mu.w_match w = some m) ∧
          ∃ m w,
            valM val_m m (mu.m_match m) < val_m m w ∧
              valW val_w w (mu.w_match w) < val_w w m)) ∧
          ((∀ m, ∃ w, mu.m_match m = some w) ∧
            ∀ w, ∃ m, mu.w_match w = some m)

/--
Theorem 2 under the completed operational stability reading of Sections 4--5.
The stability and comparison predicates are written out here, rather than
routed through paper-local wrappers, so this is the single reviewable semantic
statement of the theorem.
-/
def theorem2_applicant_optimalitySpec : Prop :=
  ∀ {Applicants Colleges : Type*}
    [Fintype Applicants] [Fintype Colleges]
    [DecidableEq Applicants] [DecidableEq Colleges]
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (happlicant_strict :
      (∀ a c c', val_applicant a c = val_applicant a c' → c = c') ∧
        ∀ a c, val_applicant a c ≠ 0)
    (hcollege_strict :
      (∀ c a a', val_college c a = val_college c a' → a = a') ∧
        ∀ c a, val_college c a ≠ 0),
    (∃ s : ExactCollegeBatchedProcedure.SourceWaitingListState
          Applicants Colleges,
        ExactCollegeBatchedProcedure.SourceReachable quota val_applicant
            val_college hcollege_strict.1 s ∧
          ¬ (∃ a, ExactCollegeBatchedProcedure.SourceActive quota
            val_applicant val_college hcollege_strict.1 s a)) ∧
      ∀ s : ExactCollegeBatchedProcedure.SourceWaitingListState
          Applicants Colleges,
        ExactCollegeBatchedProcedure.SourceReachable quota val_applicant
            val_college hcollege_strict.1 s →
          ¬ (∃ a, ExactCollegeBatchedProcedure.SourceActive quota
            val_applicant val_college hcollege_strict.1 s a) →
          ((∀ c,
              ((ExactCollegeBatchedProcedure.sourceAssignmentView quota
                val_college hcollege_strict.1 s).college_roster c).card ≤ quota c) ∧
            (∀ a, 0 ≤ ManyToOne.valApplicant val_applicant a
              ((ExactCollegeBatchedProcedure.sourceAssignmentView quota
                val_college hcollege_strict.1 s).app_match a)) ∧
            (∀ c a, a ∈
              (ExactCollegeBatchedProcedure.sourceAssignmentView quota
                val_college hcollege_strict.1 s).college_roster c →
                0 ≤ val_college c a) ∧
            (∀ a c,
              ManyToOne.valApplicant val_applicant a
                ((ExactCollegeBatchedProcedure.sourceAssignmentView quota
                  val_college hcollege_strict.1 s).app_match a) <
                val_applicant a c →
              ((0 < val_college c a ∧
                ((ExactCollegeBatchedProcedure.sourceAssignmentView quota
                  val_college hcollege_strict.1 s).college_roster c).card < quota c) ∨
                ∃ a' ∈
                  (ExactCollegeBatchedProcedure.sourceAssignmentView quota
                    val_college hcollege_strict.1 s).college_roster c,
                  val_college c a' < val_college c a) →
                False)) ∧
            ∀ (nu : ManyToOneAssignment Applicants Colleges),
              ((∀ c, (nu.college_roster c).card ≤ quota c) ∧
                (∀ a, 0 ≤ ManyToOne.valApplicant val_applicant a (nu.app_match a)) ∧
                (∀ c a, a ∈ nu.college_roster c → 0 ≤ val_college c a) ∧
                (∀ a c,
                  ManyToOne.valApplicant val_applicant a (nu.app_match a) <
                    val_applicant a c →
                  ((0 < val_college c a ∧ (nu.college_roster c).card < quota c) ∨
                    ∃ a' ∈ nu.college_roster c,
                      val_college c a' < val_college c a) →
                    False)) →
                ∀ a,
                  ManyToOne.valApplicant val_applicant a (nu.app_match a) ≤
                    ManyToOne.valApplicant val_applicant a
                      ((ExactCollegeBatchedProcedure.sourceAssignmentView quota
                        val_college hcollege_strict.1 s).app_match a)

end PaperInterface
end GS62CollegeAdmissions
