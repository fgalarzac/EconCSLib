import GS62CollegeAdmissions.BatchedProcedure
import GS62CollegeAdmissions.ManyToOneOptimality

/-!
# Auxiliary cloned-seat batching for college admissions

Section 4 of Gale--Shapley does not present college admissions as an opaque
existence argument.  In each stage, every rejected applicant applies to the
next college on her list, and a college of quota `q` retains its top `q`
applicants seen so far.

This module implements an auxiliary cloned-seat batching rule.  One scheduled
application is expanded into consecutive proposals to every still available
seat of the applicant's current best college.  Its terminal assignment agrees
with refined-seat deferred acceptance, but its intermediate stages are not the
literal Section 4 top-`q` state: an applicant provisionally accepted and then
displaced within the same fold may retain untried clones of that college.

`ExactCollegeBatchedProcedure.lean` is the source-facing model.  It records
cumulative applications directly and proves that every round replaces each
waiting list by the top `q` applicants from the old list and fresh batch.

The main bridge theorem here remains useful as a terminal-outcome certificate
for the auxiliary schedule.  It is not used as evidence for literal
round-by-round source semantics.
-/

namespace GS62CollegeAdmissions
open EconCSLib.Matching

namespace CollegeBatchedProcedure

variable {Applicants Colleges : Type*}
  [Fintype Applicants] [Fintype Colleges]
  [DecidableEq Applicants] [DecidableEq Colleges]

abbrev Seat (quota : Colleges → ℕ) :=
  ManyToOneOptimality.Seat quota

/--
One applicant's cloned-seat application block.  If the applicant is active,
choose her best remaining cloned seat and schedule her once for every remaining
seat of that same college.  The block stops there: it cannot spill into the
next college in the same auxiliary stage.
-/
noncomputable def collegeApplicationBlock
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (happNoZero : ∀ a c, val_applicant a c ≠ 0)
    (s : DAState Applicants (Seat quota))
    (a : Applicants) : List Applicants := by
  classical
  let refined := ManyToOneOptimality.refinedApplicantSeatValue
    quota val_applicant happNoZero
  by_cases hactive : IsActiveMan refined s a
  · let best : Seat quota :=
      Classical.choose (exists_best_woman refined s a hactive)
    let sameCollegeRemaining :=
      (s.m_proposals a).filter fun seat => seat.1 = best.1
    exact List.replicate sameCollegeRemaining.card a
  · exact []

/--
The applicants active at stage start, expanded into one college-application
block each.  Newly displaced applicants are not added during the fold.
-/
noncomputable def collegeBatchedSchedule
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (happNoZero : ∀ a c, val_applicant a c ≠ 0)
    (s : DAState Applicants (Seat quota)) : List Applicants :=
  let refined := ManyToOneOptimality.refinedApplicantSeatValue
    quota val_applicant happNoZero
  (gsBatchedSchedule refined s).flatMap
    (collegeApplicationBlock quota val_applicant happNoZero s)

theorem collegeApplicationBlock_shape_of_active
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (happNoZero : ∀ a c, val_applicant a c ≠ 0)
    (s : DAState Applicants (Seat quota))
    (a : Applicants)
    (hactive : IsActiveMan
      (ManyToOneOptimality.refinedApplicantSeatValue
        quota val_applicant happNoZero) s a) :
    ∃ best : Seat quota,
      BestRemainingWoman
          (ManyToOneOptimality.refinedApplicantSeatValue
            quota val_applicant happNoZero) s a best ∧
        collegeApplicationBlock quota val_applicant happNoZero s a =
          List.replicate
            ((s.m_proposals a).filter fun seat => seat.1 = best.1).card a ∧
        0 < ((s.m_proposals a).filter fun seat => seat.1 = best.1).card := by
  classical
  let refined := ManyToOneOptimality.refinedApplicantSeatValue
    quota val_applicant happNoZero
  let best : Seat quota :=
    Classical.choose (exists_best_woman refined s a hactive)
  have hbest : BestRemainingWoman refined s a best :=
    Classical.choose_spec (exists_best_woman refined s a hactive)
  refine ⟨best, hbest, ?_, ?_⟩
  · simp [collegeApplicationBlock, refined, hactive, best]
  · exact Finset.card_pos.mpr ⟨best, Finset.mem_filter.mpr ⟨hbest.1, rfl⟩⟩

theorem mem_collegeBatchedSchedule_active
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (happNoZero : ∀ a c, val_applicant a c ≠ 0)
    (s : DAState Applicants (Seat quota))
    {a : Applicants}
    (ha : a ∈ collegeBatchedSchedule quota val_applicant happNoZero s) :
    IsActiveMan
      (ManyToOneOptimality.refinedApplicantSeatValue
        quota val_applicant happNoZero) s a := by
  classical
  let refined := ManyToOneOptimality.refinedApplicantSeatValue
    quota val_applicant happNoZero
  rcases List.mem_flatMap.mp ha with ⟨a', ha', hablock⟩
  have ha'Active : IsActiveMan refined s a' :=
    (mem_gsBatchedSchedule_iff refined s a').1 ha'
  rcases collegeApplicationBlock_shape_of_active
      quota val_applicant happNoZero s a' ha'Active with
    ⟨best, _hbest, hshape, _hpositive⟩
  rw [hshape] at hablock
  have haa' : a = a' := (by simpa using hablock :
    (∃ i, ⟨best.1, i⟩ ∈ s.m_proposals a') ∧ a = a').2
  simpa [refined, haa'] using ha'Active

theorem collegeBatchedSchedule_nonempty_of_active
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (happNoZero : ∀ a c, val_applicant a c ≠ 0)
    (s : DAState Applicants (Seat quota))
    (hactive : ∃ a, IsActiveMan
      (ManyToOneOptimality.refinedApplicantSeatValue
        quota val_applicant happNoZero) s a) :
    collegeBatchedSchedule quota val_applicant happNoZero s ≠ [] := by
  classical
  rcases hactive with ⟨a, ha⟩
  rcases collegeApplicationBlock_shape_of_active
      quota val_applicant happNoZero s a ha with
    ⟨best, _hbest, hshape, hpositive⟩
  apply List.ne_nil_of_mem (a := a)
  apply List.mem_flatMap.mpr
  refine ⟨a, (mem_gsBatchedSchedule_iff _ s a).2 ha, ?_⟩
  rw [hshape]
  exact List.mem_replicate.mpr ⟨Nat.ne_of_gt hpositive, rfl⟩

/-- One complete auxiliary cloned-seat batching stage. -/
noncomputable def collegeBatchedStep
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (happNoZero : ∀ a c, val_applicant a c ≠ 0)
    (s : DAState Applicants (Seat quota)) :
    DAState Applicants (Seat quota) :=
  daStateAfterSchedule
    (ManyToOneOptimality.refinedApplicantSeatValue
      quota val_applicant happNoZero)
    (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college)
    s (collegeBatchedSchedule quota val_applicant happNoZero s)

theorem remainingProposalCount_collegeBatchedStep_add_one_of_active
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (happNoZero : ∀ a c, val_applicant a c ≠ 0)
    (s : DAState Applicants (Seat quota))
    (hactive : ∃ a, IsActiveMan
      (ManyToOneOptimality.refinedApplicantSeatValue
        quota val_applicant happNoZero) s a) :
    remainingProposalCount
        (collegeBatchedStep quota val_applicant val_college happNoZero s) + 1 ≤
      remainingProposalCount s := by
  classical
  let refined := ManyToOneOptimality.refinedApplicantSeatValue
    quota val_applicant happNoZero
  let seatValue :=
    ManyToOneAssignment.collegeSeatValue (quota := quota) val_college
  have hschedule := collegeBatchedSchedule_nonempty_of_active
    quota val_applicant happNoZero s hactive
  cases hs : collegeBatchedSchedule quota val_applicant happNoZero s with
  | nil => exact False.elim (hschedule hs)
  | cons a rest =>
      have haMem : a ∈ collegeBatchedSchedule
          quota val_applicant happNoZero s := by simp [hs]
      have haActive : IsActiveMan refined s a := by
        exact mem_collegeBatchedSchedule_active
          quota val_applicant happNoZero s haMem
      have hhead := remainingProposalCount_daStepByMan_add_one_of_active
        refined seatValue s a haActive
      have htail := daStateAfterSchedule_remainingProposalCount_le
        refined seatValue (daStepByMan refined seatValue s a) rest
      change remainingProposalCount
          (daStateAfterSchedule refined seatValue s
            (collegeBatchedSchedule quota val_applicant happNoZero s)) + 1 ≤
        remainingProposalCount s
      rw [hs, daStateAfterSchedule_cons]
      omega

theorem collegeBatchedStep_eq_self_of_not_active
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (happNoZero : ∀ a c, val_applicant a c ≠ 0)
    (s : DAState Applicants (Seat quota))
    (hnot : ¬ ∃ a, IsActiveMan
      (ManyToOneOptimality.refinedApplicantSeatValue
        quota val_applicant happNoZero) s a) :
    collegeBatchedStep quota val_applicant val_college happNoZero s = s := by
  have hschedule : collegeBatchedSchedule
      quota val_applicant happNoZero s = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro a ha
    exact hnot ⟨a, mem_collegeBatchedSchedule_active
      quota val_applicant happNoZero s ha⟩
  simp [collegeBatchedStep, hschedule]

/-- The auxiliary cloned-seat run from any state for a prescribed horizon. -/
noncomputable def collegeStateAfterBatchesFrom
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (happNoZero : ∀ a c, val_applicant a c ≠ 0) :
    DAState Applicants (Seat quota) → ℕ → DAState Applicants (Seat quota)
  | s, 0 => s
  | s, stages + 1 =>
      collegeStateAfterBatchesFrom quota val_applicant val_college happNoZero
        (collegeBatchedStep quota val_applicant val_college happNoZero s) stages

private theorem active_start_of_active_after_college_batches
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (happNoZero : ∀ a c, val_applicant a c ≠ 0)
    (s : DAState Applicants (Seat quota)) (stages : ℕ)
    (hactive : ∃ a, IsActiveMan
      (ManyToOneOptimality.refinedApplicantSeatValue
        quota val_applicant happNoZero)
      (collegeStateAfterBatchesFrom quota val_applicant val_college
        happNoZero s stages) a) :
    ∃ a, IsActiveMan
      (ManyToOneOptimality.refinedApplicantSeatValue
        quota val_applicant happNoZero) s a := by
  induction stages generalizing s with
  | zero => simpa [collegeStateAfterBatchesFrom] using hactive
  | succ stages ih =>
      have hstep := ih
        (collegeBatchedStep quota val_applicant val_college happNoZero s)
        (by simpa [collegeStateAfterBatchesFrom] using hactive)
      by_contra hnot
      rw [collegeBatchedStep_eq_self_of_not_active
        quota val_applicant val_college happNoZero s hnot] at hstep
      exact hnot hstep

private theorem remainingProposalCount_after_active_college_batches
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (happNoZero : ∀ a c, val_applicant a c ≠ 0)
    (s : DAState Applicants (Seat quota)) (stages : ℕ)
    (hactiveFinal : ∃ a, IsActiveMan
      (ManyToOneOptimality.refinedApplicantSeatValue
        quota val_applicant happNoZero)
      (collegeStateAfterBatchesFrom quota val_applicant val_college
        happNoZero s stages) a) :
    remainingProposalCount
        (collegeStateAfterBatchesFrom quota val_applicant val_college
          happNoZero s stages) + stages ≤
      remainingProposalCount s := by
  induction stages generalizing s with
  | zero => simp [collegeStateAfterBatchesFrom]
  | succ stages ih =>
      let next := collegeBatchedStep
        quota val_applicant val_college happNoZero s
      have hactiveNext : ∃ a, IsActiveMan
          (ManyToOneOptimality.refinedApplicantSeatValue
            quota val_applicant happNoZero) next a :=
        active_start_of_active_after_college_batches quota val_applicant
          val_college happNoZero next stages
          (by simpa [collegeStateAfterBatchesFrom, next] using hactiveFinal)
      have htail := ih next
        (by simpa [collegeStateAfterBatchesFrom, next] using hactiveFinal)
      have hstart : ∃ a, IsActiveMan
          (ManyToOneOptimality.refinedApplicantSeatValue
            quota val_applicant happNoZero) s a := by
        by_contra hnot
        have hself := collegeBatchedStep_eq_self_of_not_active
          quota val_applicant val_college happNoZero s hnot
        exact hnot (by simpa [next, hself] using hactiveNext)
      have hone := remainingProposalCount_collegeBatchedStep_add_one_of_active
        quota val_applicant val_college happNoZero s hstart
      change remainingProposalCount next + 1 ≤
        remainingProposalCount s at hone
      simpa [collegeStateAfterBatchesFrom, next] using (show
        remainingProposalCount
            (collegeStateAfterBatchesFrom quota val_applicant val_college
              happNoZero next stages) + (stages + 1) ≤
          remainingProposalCount s by omega)

/-- The universal finite horizon for the auxiliary cloned-seat runner. -/
noncomputable def collegeBatchedStageBound (quota : Colleges → ℕ) : ℕ :=
  Fintype.card Applicants * Fintype.card (Seat quota)

/-- State of the auxiliary cloned-seat procedure at its finite horizon. -/
noncomputable def collegeBatchedFinalState
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (happNoZero : ∀ a c, val_applicant a c ≠ 0) :
    DAState Applicants (Seat quota) :=
  collegeStateAfterBatchesFrom quota val_applicant val_college happNoZero
    (initialDAState Applicants (Seat quota))
    (collegeBatchedStageBound (Applicants := Applicants) quota)

theorem collegeBatchedFinalState_terminated
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (happNoZero : ∀ a c, val_applicant a c ≠ 0) :
    ¬ ∃ a, IsActiveMan
      (ManyToOneOptimality.refinedApplicantSeatValue
        quota val_applicant happNoZero)
      (collegeBatchedFinalState quota val_applicant val_college
        happNoZero) a := by
  intro hactive
  have hcount := remainingProposalCount_after_active_college_batches
    quota val_applicant val_college happNoZero
    (initialDAState Applicants (Seat quota))
    (collegeBatchedStageBound (Applicants := Applicants) quota)
    (by simpa [collegeBatchedFinalState] using hactive)
  have hpositive := remainingProposalCount_pos_of_active
    (ManyToOneOptimality.refinedApplicantSeatValue
      quota val_applicant happNoZero)
    (collegeBatchedFinalState quota val_applicant val_college happNoZero)
    hactive
  have hinitial : remainingProposalCount
      (initialDAState Applicants (Seat quota)) =
        collegeBatchedStageBound (Applicants := Applicants) quota := by
    simp [remainingProposalCount_initial, collegeBatchedStageBound]
  change remainingProposalCount
      (collegeBatchedFinalState quota val_applicant val_college happNoZero) +
        collegeBatchedStageBound (Applicants := Applicants) quota ≤
      remainingProposalCount (initialDAState Applicants (Seat quota)) at hcount
  omega

private theorem college_batches_invariants_and_rejections
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (happNoZero : ∀ a c, val_applicant a c ≠ 0)
    (hcollegeStrict : ∀ c a a',
      val_college c a = val_college c a' → a = a')
    (s : DAState Applicants (Seat quota)) (stages : ℕ)
    (hinv : DAInvariants
      (ManyToOneOptimality.refinedApplicantSeatValue
        quota val_applicant happNoZero)
      (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college) s)
    (hrejected : DARejectedPairImpossibleInvariant
      (ManyToOneOptimality.refinedApplicantSeatValue
        quota val_applicant happNoZero)
      (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college) s) :
    let final := collegeStateAfterBatchesFrom quota val_applicant val_college
      happNoZero s stages
    DAInvariants
        (ManyToOneOptimality.refinedApplicantSeatValue
          quota val_applicant happNoZero)
        (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college)
        final ∧
      DARejectedPairImpossibleInvariant
        (ManyToOneOptimality.refinedApplicantSeatValue
          quota val_applicant happNoZero)
        (ManyToOneAssignment.collegeSeatValue (quota := quota) val_college)
        final := by
  let refined := ManyToOneOptimality.refinedApplicantSeatValue
    quota val_applicant happNoZero
  let seatValue :=
    ManyToOneAssignment.collegeSeatValue (quota := quota) val_college
  induction stages generalizing s with
  | zero => simpa [collegeStateAfterBatchesFrom] using And.intro hinv hrejected
  | succ stages ih =>
      let schedule := collegeBatchedSchedule quota val_applicant happNoZero s
      let next := collegeBatchedStep
        quota val_applicant val_college happNoZero s
      have hinvNext : DAInvariants refined seatValue next := by
        exact daStateAfterSchedule_satisfies_invariants
          refined seatValue s schedule hinv
      have hrejectedNext : DARejectedPairImpossibleInvariant
          refined seatValue next := by
        exact daStateAfterSchedule_satisfies_rejected_pair_impossible_no_outside_tie
          refined seatValue s schedule
          (ManyToOneOptimality.refined_men_acceptably_strict
            quota val_applicant happNoZero)
          (ManyToOneOptimality.college_seat_women_strict
            quota val_college hcollegeStrict)
          (ManyToOneOptimality.refined_men_no_outside_tie
            quota val_applicant happNoZero)
          hinv hrejected
      simpa [collegeStateAfterBatchesFrom, next, schedule,
        collegeBatchedStep, refined, seatValue] using
        ih next hinvNext hrejectedNext

/-- Seat assignment produced by the auxiliary cloned-seat batched run. -/
noncomputable def collegeWaitingListSeatAssignment
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (happNoZero : ∀ a c, val_applicant a c ≠ 0) :
    Assignment Applicants (Seat quota) :=
  let s := collegeBatchedFinalState quota val_applicant val_college happNoZero
  ⟨s.m_match, s.w_match, s.consistent⟩

/-- Collapse the auxiliary cloned-seat run to college rosters. -/
noncomputable def collegeWaitingListAssignment
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (happNoZero : ∀ a c, val_applicant a c ≠ 0) :
    ManyToOneAssignment Applicants Colleges :=
  ManyToOneAssignment.ofSeatAssignment quota
    (collegeWaitingListSeatAssignment quota val_applicant val_college happNoZero)

/--
Terminal equivalence theorem: the auxiliary cloned-seat batched runner returns
exactly the refined-seat DA assignment.  This does not assert equality of its
intermediate stages with the literal Section 4 top-`q` rounds.
-/
theorem paper_gs62_college_waiting_list_refines_seat_da
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hdomain : gs_strict_college_admissions_domain
      val_applicant val_college) :
    collegeWaitingListSeatAssignment quota val_applicant val_college
        hdomain.1.2 =
      ManyToOneOptimality.refinedSeatDeferredAcceptance
        quota val_applicant val_college hdomain.1.2 := by
  rcases hdomain with ⟨⟨_happStrict, happNoZero⟩,
    ⟨hcollegeStrict, _hcollegeNoZero⟩⟩
  let refined := ManyToOneOptimality.refinedApplicantSeatValue
    quota val_applicant happNoZero
  let seatValue :=
    ManyToOneAssignment.collegeSeatValue (quota := quota) val_college
  let final := collegeBatchedFinalState
    quota val_applicant val_college happNoZero
  have hcert := college_batches_invariants_and_rejections
    quota val_applicant val_college happNoZero hcollegeStrict
    (initialDAState Applicants (Seat quota))
    (collegeBatchedStageBound (Applicants := Applicants) quota)
    (initialDAState_satisfies_invariants refined seatValue)
    (initialDAState_satisfies_rejected_pair_impossible refined seatValue)
  have hinv : DAInvariants refined seatValue final := hcert.1
  have hrejected : DARejectedPairImpossibleInvariant refined seatValue final :=
    hcert.2
  have hterm : ¬ ∃ a, IsActiveMan refined final a :=
    collegeBatchedFinalState_terminated
      quota val_applicant val_college happNoZero
  have hdaRejected : DARejectedPairImpossibleInvariant refined seatValue
      (deferredAcceptanceState refined seatValue) :=
    deferredAcceptanceState_satisfies_rejected_pair_impossible_no_outside_tie
      refined seatValue
      (ManyToOneOptimality.refined_men_acceptably_strict
        quota val_applicant happNoZero)
      (ManyToOneOptimality.college_seat_women_strict
        quota val_college hcollegeStrict)
      (ManyToOneOptimality.refined_men_no_outside_tie
        quota val_applicant happNoZero)
  change (⟨final.m_match, final.w_match, final.consistent⟩ :
      Assignment Applicants (Seat quota)) =
    deferredAcceptance refined seatValue
  exact daState_assignment_eq_deferredAcceptance_of_rejected_pair_impossible_no_outside_tie
    refined seatValue final
    (ManyToOneOptimality.refined_men_strict
      quota val_applicant happNoZero)
    (ManyToOneOptimality.refined_men_no_outside_tie
      quota val_applicant happNoZero)
    hinv hterm hrejected hdaRejected

/-- The collapsed auxiliary runner has the same terminal Theorem 2 outcome. -/
theorem paper_gs62_college_waiting_list_assignment_eq_applicant_da
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hdomain : gs_strict_college_admissions_domain
      val_applicant val_college) :
    collegeWaitingListAssignment quota val_applicant val_college hdomain.1.2 =
      ManyToOneOptimality.refinedDeferredAcceptanceManyToOne
        quota val_applicant val_college hdomain.1.2 := by
  unfold collegeWaitingListAssignment
  unfold ManyToOneOptimality.refinedDeferredAcceptanceManyToOne
  exact congrArg (ManyToOneAssignment.ofSeatAssignment quota)
    (paper_gs62_college_waiting_list_refines_seat_da
      quota val_applicant val_college hdomain)

end CollegeBatchedProcedure
end GS62CollegeAdmissions
