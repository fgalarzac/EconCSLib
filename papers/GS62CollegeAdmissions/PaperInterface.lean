import GS62CollegeAdmissions.BatchedProcedure
import GS62CollegeAdmissions.ExactCollegeBatchedProcedure
import GS62CollegeAdmissions.SourceStability

/-!
# Paper Interface: Gale--Shapley 1962

Compact source-facing surface for Gale and Shapley's *College Admissions and
the Stability of Marriage*.  The normal review surface covers the displayed
college definitions, the prose marriage-instability definition, and Theorems 1
and 2.  Procedure lemmas and the paper's examples remain visible as support,
but examples and unnumbered prose consequences are deep-audit material rather
than normal named-theory targets.

For the college model, the page-10 displayed replacement-pair definition is
exposed separately from the completed standard matching convention used by the
paper's runners and the reusable many-to-one library.  The latter additionally
rules out unacceptable assignments, blocks involving vacant seats, and blocks
by unmatched applicants.  `SourceStability.lean` proves the exact bridge and a
small boundary counterexample, so this interface does not hide that completion
inside a source-definition row.
-/

namespace GS62CollegeAdmissions
namespace PaperInterface

open EconCSLib.Matching

/-! ## Source definitions -/

/--
Strict complete marriage domain.
Source status: direct paper model condition.
Source note: Section 3 gives each participant a strict ranking of every member
of the opposite finite community.
-/
def strictMarriageDomain {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  MenStrictPreferenceProfile val_m ∧
    WomenStrictPreferenceProfile val_w ∧
    AllPairsAcceptable val_m val_w

/--
Lean-checked unfolding of the paper's strict complete marriage domain.
Source status: direct source-definition fidelity theorem.
-/
theorem strictMarriageDomain_iff_source_definition {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    strictMarriageDomain val_m val_w ↔
      MenStrictPreferenceProfile val_m ∧
        WomenStrictPreferenceProfile val_w ∧
        AllPairsAcceptable val_m val_w := by
  rfl

/--
The Section 3 prose definition of an unstable set of marriages: some man and
woman prefer one another to their current mates.  The source's surrounding
marriage domain is complete, so the optional-partner values below always
evaluate at actual mates on source-domain uses.
Source status: direct paper definition.
-/
def unstableMarriage {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) : Prop :=
  ∃ m w,
    valM val_m m (mu.m_match m) < val_m m w ∧
      valW val_w w (mu.w_match w) < val_w w m

/-- Exact closed proposition for the Section 3 marriage-instability definition. -/
def unstableMarriage_iff_source_definitionSpec : Prop :=
  ∀ {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W),
    unstableMarriage val_m val_w mu ↔
      ∃ m w,
        valM val_m m (mu.m_match m) < val_m m w ∧
          valW val_w w (mu.w_match w) < val_w w m

theorem unstableMarriage_iff_source_definition :
    unstableMarriage_iff_source_definitionSpec := by
  intro M W val_m val_w mu
  rfl

/--
Completed operational marriage stability used by the reusable matching API:
individual rationality and no blocking pair.  On the paper's complete,
all-pairs-acceptable marriage domain, its no-blocking component is exactly the
negation of `unstableMarriage` above.
Source status: operational completion used by theorem proofs.
-/
def stableMarriage {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) : Prop :=
  (∀ m, 0 ≤ valM val_m m (mu.m_match m)) ∧
    (∀ w, 0 ≤ valW val_w w (mu.w_match w)) ∧
      ∀ m w, valM val_m m (mu.m_match m) < val_m m w →
        valW val_w w (mu.w_match w) < val_w w m → False

/-- Lean-checked unfolding of the completed operational stability predicate. -/
theorem stableMarriage_iff_completed_standard_definition {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) :
    stableMarriage val_m val_w mu ↔
      (∀ m, 0 ≤ valM val_m m (mu.m_match m)) ∧
        (∀ w, 0 ≤ valW val_w w (mu.w_match w)) ∧
          ∀ m w, valM val_m m (mu.m_match m) < val_m m w →
            valW val_w w (mu.w_match w) < val_w w m → False := by
  rfl

/--
Complete marriage: every participant on both sides is matched.
Source status: direct paper model condition.
-/
def completeMarriage {M W : Type*} (mu : Assignment M W) : Prop :=
  (∀ m, ∃ w, mu.m_match m = some w) ∧
    ∀ w, ∃ m, mu.w_match w = some m

/--
Lean-checked unfolding of the paper's complete-marriage condition.
Source status: direct source-definition fidelity theorem.
-/
theorem completeMarriage_iff_source_definition {M W : Type*}
    (mu : Assignment M W) :
    completeMarriage mu ↔
      (∀ m, ∃ w, mu.m_match m = some w) ∧
        ∀ w, ∃ m, mu.w_match w = some m := by
  rfl

/--
The finite strict arbitrary-quota college-admissions domain of Section 2.
Positive values are listed/acceptable pairs and negative values are omitted
pairs; zero is the outside option.  Injective negative values are a numerical
extension of the source's unranked omitted alternatives and cannot enter the
mutually eligible source procedure.
Source status: direct paper model condition.
-/
def strictCollegeAdmissionsDomain {Applicants Colleges : Type*}
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ) : Prop :=
  gs_strict_college_admissions_domain val_applicant val_college

/--
Lean-checked unfolding of the paper's strict college-admissions domain.
Source status: direct source-definition fidelity theorem.
-/
theorem strictCollegeAdmissionsDomain_iff_source_definition
    {Applicants Colleges : Type*}
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ) :
    strictCollegeAdmissionsDomain val_applicant val_college ↔
      ApplicantsStrictCollegeProfile val_applicant ∧
        CollegesStrictApplicantProfile val_college := by
  rfl

/--
Section 4 application-permission rule for one applicant-college pair: the
applicant is willing to attend and the college is willing to consider that
applicant.  This filters the procedure's available applications; it is not a
global restriction saying that every college acceptable to an applicant must
also accept that applicant.
Source status: direct Section 4 procedure condition.
-/
def permittedCollegeApplication {Applicants Colleges : Type*}
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (a : Applicants) (c : Colleges) : Prop :=
  0 < val_applicant a c ∧ 0 < val_college c a

/--
Lean-checked unfolding of the Section 4 application-permission condition.
This stays separate from `strictCollegeAdmissionsDomain` because it governs
which applications the procedure may make, rather than preference strictness.
Source status: direct source-definition fidelity theorem.
-/
theorem permittedCollegeApplication_iff_source_definition
    {Applicants Colleges : Type*}
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (a : Applicants) (c : Colleges) :
    permittedCollegeApplication val_applicant val_college a c ↔
      0 < val_applicant a c ∧ 0 < val_college c a := by
  rfl

/--
A feasible college assignment respects every college quota.
Source status: direct paper model condition.
-/
def feasibleCollegeAssignment {Applicants Colleges : Type*}
    (quota : Colleges → ℕ)
    (mu : ManyToOneAssignment Applicants Colleges) : Prop :=
  gs_feasible_college_assignment quota mu

/--
Lean-checked unfolding of the paper's quota-feasibility definition.
Source status: direct source-definition fidelity theorem.
-/
theorem feasibleCollegeAssignment_iff_source_definition
    {Applicants Colleges : Type*}
    (quota : Colleges → ℕ)
    (mu : ManyToOneAssignment Applicants Colleges) :
    feasibleCollegeAssignment quota mu ↔
      ManyToOneAssignment.RespectsQuota quota mu := by
  rfl


/--
The literal replacement-pair condition in the first displayed definition on
page 10.  It requires both the displaced applicant and the moving applicant
to be currently assigned, exactly as printed.
Source status: direct paper definition.
-/
def replacementPairCollegeInstability {Applicants Colleges : Type*}
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : ManyToOneAssignment Applicants Colleges) : Prop :=
  gs62ReplacementPair val_applicant val_college mu

/--
Lean-checked literal unfolding of the displayed replacement-pair definition.
Source status: direct source-definition fidelity theorem.
-/
theorem replacementPairCollegeInstability_iff_source_definition
    {Applicants Colleges : Type*}
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : ManyToOneAssignment Applicants Colleges) :
    replacementPairCollegeInstability val_applicant val_college mu ↔
      ∃ alpha beta A B,
        mu.app_match alpha = some A ∧
          mu.app_match beta = some B ∧
            val_applicant beta B < val_applicant beta A ∧
              val_college A alpha < val_college A beta := by
  exact gs62ReplacementPair_iff_source_definition val_applicant val_college mu

/--
The literal negation of the page-10 replacement-pair condition.
Source status: direct paper definition, not the completed standard convention.
-/
def literalStableCollegeAssignment {Applicants Colleges : Type*}
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : ManyToOneAssignment Applicants Colleges) : Prop :=
  gs62LiteralStableCollegeAssignment val_applicant val_college mu

/--
Lean-checked literal unfolding of the source's no-replacement condition.
Source status: direct source-definition fidelity theorem.
-/
theorem literalStableCollegeAssignment_iff_source_definition
    {Applicants Colleges : Type*}
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : ManyToOneAssignment Applicants Colleges) :
    literalStableCollegeAssignment val_applicant val_college mu ↔
      ¬ replacementPairCollegeInstability val_applicant val_college mu := by
  rfl

/--
The completed standard stability convention used by the Lean runner and by the
arbitrary-quota optimality proof.  In addition to the literal page-10
replacement-pair condition, it requires quota feasibility, individual
rationality, and no blocks through an empty seat or an unmatched applicant.
Source status: explicit completed matching convention; not a literal
source-definition claim.
-/
def stableCollegeAssignment {Applicants Colleges : Type*}
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : ManyToOneAssignment Applicants Colleges) : Prop :=
  gs62StandardStableCollegeAssignment quota val_applicant val_college mu

/--
Lean-checked unfolding of the completed standard matching convention.
Source status: operational convention theorem, not a source-definition row.
-/
theorem stableCollegeAssignment_iff_completed_standard_definition
    {Applicants Colleges : Type*}
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : ManyToOneAssignment Applicants Colleges) :
    stableCollegeAssignment quota val_applicant val_college mu ↔
      ManyToOne.IsStable val_applicant val_college quota mu := by
  exact gs62StandardStableCollegeAssignment_iff_standard_definition
    quota val_applicant val_college mu

/--
Every completed-standard stable assignment satisfies the literal source
no-replacement condition.  No fullness or acceptability assumption is needed
in this direction.
Source status: proved bridge from the explicit operational convention.
-/
theorem standardStable_implies_literalStableCollegeAssignment
    {Applicants Colleges : Type*}
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : ManyToOneAssignment Applicants Colleges) :
    stableCollegeAssignment quota val_applicant val_college mu →
      literalStableCollegeAssignment val_applicant val_college mu :=
  gs62LiteralStable_of_standardStable quota val_applicant val_college mu

/--
The source's displayed unstable-assignment condition, with no completion
clauses added.
Source status: direct paper definition.
-/
def unstableCollegeAssignment {Applicants Colleges : Type*}
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : ManyToOneAssignment Applicants Colleges) : Prop :=
  replacementPairCollegeInstability val_applicant val_college mu

/--
Lean-checked unfolding of the literal unstable-assignment condition.
Source status: direct source-definition fidelity theorem.
-/
def unstableCollegeAssignment_iff_source_definitionSpec : Prop :=
  ∀ {Applicants Colleges : Type*}
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : ManyToOneAssignment Applicants Colleges),
    unstableCollegeAssignment val_applicant val_college mu ↔
      replacementPairCollegeInstability val_applicant val_college mu

theorem unstableCollegeAssignment_iff_source_definition :
    unstableCollegeAssignment_iff_source_definitionSpec := by
  intro Applicants Colleges val_applicant val_college mu
  rfl

/--
The second displayed definition on page 10, read over the literal
no-replacement stability predicate and the surrounding fixed-quota assignment
domain.  Feasibility is written explicitly because the Lean assignment
structure itself enforces consistency but not quotas.  It is deliberately distinct from
`applicantOptimalCollegeAssignment`, which records the completed-standard
convention used by the formal Theorem 2 route.
Source status: direct paper definition.
-/
def literalApplicantOptimalCollegeAssignment {Applicants Colleges : Type*}
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : ManyToOneAssignment Applicants Colleges) : Prop :=
  feasibleCollegeAssignment quota mu ∧
    literalStableCollegeAssignment val_applicant val_college mu ∧
      ∀ nu, feasibleCollegeAssignment quota nu →
        literalStableCollegeAssignment val_applicant val_college nu →
          ∀ a,
            ManyToOne.valApplicant val_applicant a (nu.app_match a) ≤
              ManyToOne.valApplicant val_applicant a (mu.app_match a)

/--
Lean-checked exact unfolding of the second page-10 definition over the
fixed-quota feasible domain and literal stability.
Source status: direct source-definition fidelity theorem.
-/
def literalApplicantOptimalCollegeAssignment_iff_source_definitionSpec : Prop :=
  ∀ {Applicants Colleges : Type*}
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : ManyToOneAssignment Applicants Colleges),
    literalApplicantOptimalCollegeAssignment quota val_applicant val_college mu ↔
      feasibleCollegeAssignment quota mu ∧
        literalStableCollegeAssignment val_applicant val_college mu ∧
          ∀ nu, feasibleCollegeAssignment quota nu →
            literalStableCollegeAssignment val_applicant val_college nu →
              ∀ a,
                ManyToOne.valApplicant val_applicant a (nu.app_match a) ≤
                  ManyToOne.valApplicant val_applicant a (mu.app_match a)

theorem literalApplicantOptimalCollegeAssignment_iff_source_definition :
    literalApplicantOptimalCollegeAssignment_iff_source_definitionSpec := by
  intro Applicants Colleges quota val_applicant val_college mu
  rfl

/--
Applicant optimality over the completed standard stability convention used by
the Lean theorem route.  The page-10 phrase "other stable assignment" cannot
be read as the raw replacement-pair predicate alone: the boundary witness
above permits an unmatched applicant to be ignored.  This predicate makes the
completion explicit instead of hiding it in the word "stable".
Source status: completed-convention interpretation of the paper's definition.
-/
def applicantOptimalCollegeAssignment {Applicants Colleges : Type*}
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : ManyToOneAssignment Applicants Colleges) : Prop :=
  gs_applicant_optimal_college_assignment quota val_applicant val_college mu

/--
Lean-checked unfolding of applicant optimality over completed-standard stable
assignments.
Source status: operational convention theorem, not a literal source-definition
row.
-/
theorem applicantOptimalCollegeAssignment_iff_completed_standard_definition
    {Applicants Colleges : Type*}
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : ManyToOneAssignment Applicants Colleges) :
    applicantOptimalCollegeAssignment quota val_applicant val_college mu ↔
      stableCollegeAssignment quota val_applicant val_college mu ∧
        ∀ nu, stableCollegeAssignment quota val_applicant val_college nu →
          ∀ a, ManyToOne.valApplicant val_applicant a (nu.app_match a) ≤
            ManyToOne.valApplicant val_applicant a (mu.app_match a) := by
  rfl

/--
College optimality under the explicit responsive cloned-seat extension of each
college's strict applicant ranking to quota-sized rosters, together with the
completed standard stability convention.  This declaration makes the paper's
otherwise unstated roster-order choice visible.
Source status: recorded responsive/standard completion of the quoted "college
optimal" condition on page 14.
-/
def responsiveCollegeOptimalAssignment {Applicants Colleges : Type*}
    [Fintype Applicants] [Fintype Colleges]
    [DecidableEq Applicants] [DecidableEq Colleges]
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : ManyToOneAssignment Applicants Colleges) : Prop :=
  ManyToOneOptimality.gs_responsive_college_optimal_assignment
    quota val_applicant val_college mu

/--
Lean-checked unfolding of responsive college optimality under the explicit
responsive/standard completion.
Source status: operational convention theorem, not a literal source-definition
row.
-/
theorem responsiveCollegeOptimalAssignment_iff_completed_standard_definition
    {Applicants Colleges : Type*}
    [Fintype Applicants] [Fintype Colleges]
    [DecidableEq Applicants] [DecidableEq Colleges]
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : ManyToOneAssignment Applicants Colleges) :
    responsiveCollegeOptimalAssignment quota val_applicant val_college mu ↔
      stableCollegeAssignment quota val_applicant val_college mu ∧
        ∀ nu, stableCollegeAssignment quota val_applicant val_college nu →
          ManyToOneOptimality.gs_colleges_weakly_prefer_assignment
            quota val_college mu nu := by
  rfl

/-! ## The three source examples -/

/--
Example 1 has exactly the three stable marriages displayed by the paper.
Source status: direct paper example.
-/
theorem example1_exactly_three_stable_marriages :
    ∀ partner : Fin 3 → Fin 3,
      StableRankMatching example1MenRank example1WomenRank partner ↔
        partner = example1MenFirst ∨ partner = example1WomenFirst ∨
          partner = example1AllSecond :=
  paper_gs62_example1_exactly_three_stable_marriages

/--
Example 2's displayed marriage is stable and is the unique stable marriage.
Source status: direct paper example.
-/
theorem example2_unique_stable_marriage :
    StableRankMatching example2MenRank example2WomenRank example2Partner ∧
      ∀ partner : Fin 4 → Fin 4,
        StableRankMatching example2MenRank example2WomenRank partner →
          partner = example2Partner :=
  paper_gs62_example2_unique_stable_marriage

/--
Example 3 has no stable roommate pairing, independently of the fourth list.
Source status: direct paper example.
-/
theorem example3_no_stable_roommate_pairing :
    ∀ fourthRank partner : Fin 4 → Fin 4,
      ¬ StableRoommateRankTable (example3Rank fourthRank) partner :=
  paper_gs62_example3_no_stable_roommate_pairing

/-! ## Marriage procedure and results -/

/--
Theorem 1: every finite complete strict equal-side marriage market has a stable
complete marriage.
Source status: direct paper theorem.
-/
def theorem1_stable_marriage_existsSpec : Prop :=
  ∀ {M W : Type*} [Fintype M] [Fintype W]
    [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ),
    Fintype.card M = Fintype.card W →
      strictMarriageDomain val_m val_w →
      ∃ mu : Assignment M W,
        ¬ unstableMarriage val_m val_w mu ∧ completeMarriage mu

theorem theorem1_stable_marriage_exists :
    theorem1_stable_marriage_existsSpec := by
  intro M W _ _ _ _ val_m val_w hcard hdomain
  rcases paper_gs62_theorem1_stable_marriage_exists
      val_m val_w hcard hdomain with ⟨mu, hstable, hcomplete⟩
  refine ⟨mu, ?_, hcomplete⟩
  intro hunstable
  rcases hunstable with ⟨m, w, hm, hw⟩
  exact hstable.2.2 m w hm hw

/--
The paper's batched proposer procedure returns a stable marriage.
Source status: direct algorithm-and-correctness result.
-/
theorem marriage_batched_procedure_stable
    {A : Type*} [Fintype A] [DecidableEq A]
    (val_m : A → A → ℝ) (val_w : A → A → ℝ)
    (hnonempty : 0 < Fintype.card A)
    (hdomain : strictMarriageDomain val_m val_w) :
    stableMarriage val_m val_w
      (gsBatchedDeferredAcceptance val_m val_w) := by
  exact paper_gs62_batched_procedure_stable
    val_m val_w rfl hnonempty hdomain.2.2

/--
The source batched procedure ends within `n² - 2n + 2` stages, represented
over naturals as `(n - 1) * (n - 1) + 1`.
Source status: direct printed runtime claim.
-/
theorem marriage_batched_stage_bound
    {A : Type*} [Fintype A] [DecidableEq A]
    (val_m : A → A → ℝ) (val_w : A → A → ℝ)
    (hnonempty : 0 < Fintype.card A)
    (hdomain : strictMarriageDomain val_m val_w) :
    ¬ ∃ m, IsActiveMan val_m
      (gsStateAfterBatches val_m val_w
        (gsBatchedStageBound (Fintype.card A))) m := by
  exact paper_gs62_batched_stage_bound
    val_m val_w rfl hnonempty hdomain.2.2

/--
With unequal finite sides, the smaller side is fully matched and someone on a
strictly larger side remains unmatched.
Source status: direct Section 3 extension.
-/
theorem unequal_sides_deferred_acceptance
    {M W : Type*} [Fintype M] [Fintype W]
    [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hdomain : strictMarriageDomain val_m val_w) :
    stableMarriage val_m val_w (deferredAcceptance val_m val_w) ∧
      (Fintype.card M < Fintype.card W →
        (∀ m, ∃ w, (deferredAcceptance val_m val_w).m_match m = some w) ∧
        ∃ w, (deferredAcceptance val_m val_w).w_match w = none) ∧
      (Fintype.card W < Fintype.card M →
        (∀ w, ∃ m, (deferredAcceptance val_m val_w).w_match w = some m) ∧
        ∃ m, (deferredAcceptance val_m val_w).m_match m = none) := by
  exact paper_gs62_unequal_sides_deferred_acceptance
    val_m val_w hdomain.2.2

/--
Receiver-proposing DA is stable and receiver-optimal.
Source status: direct symmetric-procedure claim.
-/
theorem receiver_proposing_stable_and_optimal
    {M W : Type*} [Fintype M] [Fintype W]
    [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hdomain : strictMarriageDomain val_m val_w) :
    stableMarriage val_m val_w (womenDeferredAcceptance val_m val_w) ∧
      ∀ mu, stableMarriage val_m val_w mu → ∀ w,
        valW val_w w (mu.w_match w) ≤
          valW val_w w
            ((womenDeferredAcceptance val_m val_w).w_match w) := by
  exact paper_gs62_receiver_proposing_stable_and_optimal
    val_m val_w hdomain

/--
Equal-side specialization of the prose consequence that proposer- and
receiver-proposing outcomes agree exactly when the stable marriage is unique.
The source states the surrounding discussion after mentioning unequal sides;
this support theorem is therefore not used for normal source-claim credit.
Source status: proved support specialization; unequal-side prose remains
deep-audit material.
-/
theorem two_da_outcomes_agree_iff_unique_stable_marriage
    {M W : Type*} [Fintype M] [Fintype W]
    [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : strictMarriageDomain val_m val_w) :
    deferredAcceptance val_m val_w = womenDeferredAcceptance val_m val_w ↔
      ∃! mu : Assignment M W, stableMarriage val_m val_w mu := by
  exact paper_gs62_two_da_outcomes_agree_iff_unique_stable_marriage
    val_m val_w hcard hdomain

/-! ## College procedure and results -/

/--
Checked algorithm bridge: the paper's direct batched top-`q` waiting-list
procedure has exactly the applicant-proposing deferred-acceptance assignment.
Source status: direct algorithm-semantics bridge.
-/
theorem college_waiting_list_agrees_with_applicant_da
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
  ExactCollegeBatchedProcedure.paper_gs62_source_waiting_list_assignment_eq_applicant_da
    quota val_applicant val_college hdomain

/--
The paper's arbitrary-quota waiting-list procedure satisfies the completed
standard stability convention.  This is stronger than the literal page-10
replacement-pair condition; the direct literal consequence is exposed below.
Source status: Section 4 result under the explicit completed convention.
-/
theorem college_waiting_list_procedure_stable
    {Applicants Colleges : Type*}
    [Fintype Applicants] [Fintype Colleges]
    [DecidableEq Applicants] [DecidableEq Colleges]
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hdomain : strictCollegeAdmissionsDomain val_applicant val_college) :
    stableCollegeAssignment quota val_applicant val_college
      (ExactCollegeBatchedProcedure.sourceWaitingListFinalAssignment
        quota val_applicant val_college hdomain.2.1) :=
  ExactCollegeBatchedProcedure.paper_gs62_source_waiting_list_assignment_stable
    quota val_applicant val_college hdomain

/--
Direct literal consequence for the page-10 definition: the waiting-list
outcome has no replacement pair of two currently assigned applicants.
Source status: direct source-definition consequence of the checked Section 4
runner; it does not collapse the literal and completed conventions.
-/
theorem college_waiting_list_procedure_literal_stable
    {Applicants Colleges : Type*}
    [Fintype Applicants] [Fintype Colleges]
    [DecidableEq Applicants] [DecidableEq Colleges]
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hdomain : strictCollegeAdmissionsDomain val_applicant val_college) :
    literalStableCollegeAssignment val_applicant val_college
      (ExactCollegeBatchedProcedure.sourceWaitingListFinalAssignment
        quota val_applicant val_college hdomain.2.1) :=
  standardStable_implies_literalStableCollegeAssignment
    quota val_applicant val_college
    (ExactCollegeBatchedProcedure.sourceWaitingListFinalAssignment
      quota val_applicant val_college hdomain.2.1)
    (college_waiting_list_procedure_stable
      quota val_applicant val_college hdomain)

/--
Theorem 2 under the explicit completed standard stability convention: every
applicant weakly prefers the arbitrary-quota waiting-list outcome to every
other completed-standard stable college assignment.  The raw page-10
replacement-pair condition alone is too weak for this comparison, as the
boundary witness above proves; this theorem makes the required completion
visible rather than treating it as part of the displayed definition.
Source status: source theorem formalized under the recorded completed
stability convention.
-/
def theorem2_applicant_optimalitySpec : Prop :=
  ∀ {Applicants Colleges : Type*}
    [Fintype Applicants] [Fintype Colleges]
    [DecidableEq Applicants] [DecidableEq Colleges]
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hdomain : strictCollegeAdmissionsDomain val_applicant val_college),
    (∃ s : ExactCollegeBatchedProcedure.SourceWaitingListState
          Applicants Colleges,
        ExactCollegeBatchedProcedure.SourceReachable quota val_applicant
            val_college hdomain.2.1 s ∧
          ¬ (∃ a, ExactCollegeBatchedProcedure.SourceActive quota
            val_applicant val_college hdomain.2.1 s a)) ∧
      ∀ s : ExactCollegeBatchedProcedure.SourceWaitingListState
          Applicants Colleges,
        ExactCollegeBatchedProcedure.SourceReachable quota val_applicant
            val_college hdomain.2.1 s →
          ¬ (∃ a, ExactCollegeBatchedProcedure.SourceActive quota
            val_applicant val_college hdomain.2.1 s a) →
          applicantOptimalCollegeAssignment quota val_applicant val_college
            (ExactCollegeBatchedProcedure.sourceAssignmentView quota
              val_college hdomain.2.1 s)

theorem theorem2_applicant_optimality :
    theorem2_applicant_optimalitySpec := by
  intro Applicants Colleges _ _ _ _ quota val_applicant val_college hdomain
  constructor
  · exact
      ⟨ExactCollegeBatchedProcedure.sourceWaitingListFinalState quota
          val_applicant val_college hdomain.2.1,
        ExactCollegeBatchedProcedure.sourceWaitingListFinalState_reachable
          quota val_applicant val_college hdomain.2.1,
        ExactCollegeBatchedProcedure.sourceWaitingListFinalState_terminated
          quota val_applicant val_college hdomain.2.1⟩
  · intro s hreachable hterminal
    exact
      ExactCollegeBatchedProcedure.paper_gs62_source_reachable_terminal_assignment_applicant_optimal
        quota val_applicant val_college hdomain s hreachable hterminal

/--
Under the explicit responsive cloned-seat roster convention, the inverted
college-proposing procedure yields the unique completed-standard responsive
college-optimal assignment.  The conclusion does not require an additional
fixed-seat optimality certificate.
Source status: page-14 procedure and optimality claim under the recorded
responsive/standard completion.
-/
theorem inverted_college_proposing_unique_responsive_college_optimal
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
        val_college nu → nu = mu := by
  exact
    GS62CollegeAdmissions.ManyToOneOptimality.paper_gs62_inverted_college_proposing_responsive_outcome_unique
      quota val_applicant val_college hdomain

end PaperInterface
end GS62CollegeAdmissions
