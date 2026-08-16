import LG21TestOptionalPolicies.RecalibratedBranchMemberEntry

/-!
# Closed candidate branches under recalibrated PBOs

The source model says that the school knows the decision functions and uses
the PBO induced by them.  Consequently, a candidate action profile cannot be
accepted merely because a chosen high-type cohort benefits: after the
candidate's own public branches have been recalibrated, every eligible outside
type with a strict gain must also choose the active branch, up to source-law
null sets.

This module states that closure semantically.  It is intentionally generic in
the action implementation: `reportBranch` is an observable candidate branch,
`eligible` is the population that can choose it, and `gain` is evaluated from
the candidate profile's own PBOs.  The `PositiveMassPBOCandidateProfile`
carrier supplies those PBO obligations on its positive branches; no value is
assigned to a null branch.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace PositiveMassPBOCandidateProfile

variable
    {Omega ReportInfo NoReportInfo : Type*}
    [MeasurableSpace Omega] [MeasurableSpace ReportInfo]
    [MeasurableSpace NoReportInfo]
    {μ : Measure Omega} [IsFiniteMeasure μ] {skill : Omega -> ℝ}

/--
An observable candidate branch is closed under its recalibrated strict-gain
test when, almost everywhere among eligible students, strict gain implies
membership in that branch.  Equivalently, no eligible nonmember has a strict
gain after the candidate profile's positive branches determine their own PBOs.

The predicate does not refer to a strategy-function name or to a hidden
membership label.  A source bridge must instantiate `gain` from the literal
candidate action law and the PBOs carried by `P`.
-/
def RecalibratedCandidateBranchClosedUnderStrictGain
    (P : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := μ) (skill := skill))
    (eligible : Set Omega)
    (gain : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := μ) (skill := skill) -> Omega -> ℝ) : Prop :=
  ∀ᵐ omega ∂μ.restrict eligible,
    0 < gain P omega -> omega ∈ P.reportBranch

/--
A candidate profile is admissible for a binary source-equilibrium refinement
when its two actual public branches have positive mass, its reported branch
contains only eligible students and weakly benefits its members, and it is
closed against strict gains by eligible outsiders.  Positivity makes the
carrier's two literal PBO identities available through
`reportPBO_consistent_if_positive` and `noReportPBO_consistent_if_positive`.
-/
structure RecalibratedCandidateBranchAdmissible
    (P : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := μ) (skill := skill))
    (eligible : Set Omega)
    (gain : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := μ) (skill := skill) -> Omega -> ℝ) : Prop where
  report_mass_positive : 0 < P.reportMass
  noReport_mass_positive : 0 < P.noReportMass
  report_members_eligible : ∀ᵐ omega ∂μ.restrict P.reportBranch,
    omega ∈ eligible
  report_members_nonnegative_gain : ∀ᵐ omega ∂μ.restrict P.reportBranch,
    0 ≤ gain P omega
  strict_gain_closure :
    RecalibratedCandidateBranchClosedUnderStrictGain P eligible gain

/-- A closed candidate has a literal PBO on its positive report branch. -/
theorem RecalibratedCandidateBranchAdmissible.reportPBO
    {P : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := μ) (skill := skill)}
    {eligible : Set Omega}
    {gain : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := μ) (skill := skill) -> Omega -> ℝ}
    (H : RecalibratedCandidateBranchAdmissible P eligible gain) :
    Integrable skill (μ.restrict P.reportBranch) ∧
      (fun omega => P.reportPBO.estimate (P.reportObservation omega)) =ᵐ[
        μ.restrict P.reportBranch]
        (μ.restrict P.reportBranch)[skill |
          MeasurableSpace.comap P.reportObservation inferInstance] := by
  exact P.reportPBO_consistent_if_positive H.report_mass_positive

/-- A closed candidate has a literal PBO on its positive no-report branch. -/
theorem RecalibratedCandidateBranchAdmissible.noReportPBO
    {P : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := μ) (skill := skill)}
    {eligible : Set Omega}
    {gain : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := μ) (skill := skill) -> Omega -> ℝ}
    (H : RecalibratedCandidateBranchAdmissible P eligible gain) :
    Integrable skill (μ.restrict P.noReportBranch) ∧
      (fun omega => P.noReportPBO.estimate (P.noReportObservation omega)) =ᵐ[
        μ.restrict P.noReportBranch]
        (μ.restrict P.noReportBranch)[skill |
          MeasurableSpace.comap P.noReportObservation inferInstance] := by
  exact P.noReportPBO_consistent_if_positive H.noReport_mass_positive

/--
The strict-gain formulation is equivalent to the familiar condition that an
eligible student outside the candidate branch has nonpositive candidate gain,
almost everywhere.  This form is useful when a Gaussian calculation produces
an inequality rather than a Boolean action comparison.
-/
theorem recalibratedCandidateBranch_closedUnderStrictGain_iff
    (P : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := μ) (skill := skill))
    (eligible : Set Omega)
    (gain : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := μ) (skill := skill) -> Omega -> ℝ) :
    RecalibratedCandidateBranchClosedUnderStrictGain P eligible gain ↔
      (∀ᵐ omega ∂μ.restrict eligible,
        omega ∉ P.reportBranch -> gain P omega ≤ 0) := by
  constructor
  · intro hclosed
    filter_upwards [hclosed] with omega hclosed houtside
    by_contra hnot
    have hpositive : 0 < gain P omega := lt_of_not_ge hnot
    exact houtside (hclosed hpositive)
  · intro hclosed
    filter_upwards [hclosed] with omega hclosed
    intro hpositive
    by_contra houtside
    exact (not_lt_of_ge (hclosed houtside)) hpositive

/--
If a positive-mass eligible set is outside a candidate branch and each of its
members has strict recalibrated gain, that candidate is not closed.  This is
the formal form of the high-band diagnostic: a proposed high band is not an
admissible candidate equilibrium when a positive-mass lower band also gains
from joining the same observable branch.
-/
theorem not_recalibratedCandidateBranchClosedUnderStrictGain_of_positive_outside_gain
    (P : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := μ) (skill := skill))
    (eligible : Set Omega)
    (gain : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := μ) (skill := skill) -> Omega -> ℝ)
    (heligible : MeasurableSet eligible)
    (houtside : 0 < μ (eligible ∩ P.reportBranchᶜ))
    (hgain : ∀ omega, omega ∈ eligible ∩ P.reportBranchᶜ ->
      0 < gain P omega) :
    ¬ RecalibratedCandidateBranchClosedUnderStrictGain P eligible gain := by
  intro hclosed
  have hclosedOutside : ∀ᵐ omega ∂μ.restrict
      (eligible ∩ P.reportBranchᶜ),
      0 < gain P omega -> omega ∈ P.reportBranch := by
    exact ae_restrict_of_ae_restrict_of_subset inter_subset_left hclosed
  have houtsideMeasurable : MeasurableSet (eligible ∩ P.reportBranchᶜ) :=
    heligible.inter P.reportBranch_measurable.compl
  have hmember : ∀ᵐ omega ∂μ.restrict (eligible ∩ P.reportBranchᶜ),
      omega ∈ eligible ∩ P.reportBranchᶜ :=
    ae_restrict_mem houtsideMeasurable
  have hfalse : ∀ᵐ omega ∂μ.restrict
      (eligible ∩ P.reportBranchᶜ), False := by
    filter_upwards [hclosedOutside, hmember] with omega hclosedOutside hmember
    exact hmember.2 (hclosedOutside (hgain omega hmember))
  have hzeroRestrict : μ.restrict (eligible ∩ P.reportBranchᶜ) Set.univ = 0 := by
    rw [ae_iff] at hfalse
    simpa using hfalse
  have hzero : μ (eligible ∩ P.reportBranchᶜ) = 0 := by
    simpa using hzeroRestrict
  exact (ne_of_gt houtside) hzero

end PositiveMassPBOCandidateProfile

/-! ## Scalar upper-tail closure -/

/--
The binary best-response condition for a scalar upper-tail candidate.  This
is deliberately stated in payoff space, without assuming that the source
action function has a particular name or representation.
-/
def ScalarUpperTailClosedUnderGain (gain : ℝ -> ℝ) (cutoff : ℝ) : Prop :=
  (∀ skill, cutoff ≤ skill -> 0 ≤ gain skill) ∧
    ∀ skill, skill < cutoff -> gain skill ≤ 0

/--
At a zero-gain boundary, strict monotonicity of the expected candidate payoff
in latent skill gives the full upper-tail best-response condition.  In
particular it gives the low-band non-entry half that a one-shot high-band
candidate lacks.
-/
theorem scalarUpperTailClosedUnderGain_of_strictMono_root
    (gain : ℝ -> ℝ) (cutoff : ℝ)
    (hmono : StrictMono gain) (hroot : gain cutoff = 0) :
    ScalarUpperTailClosedUnderGain gain cutoff := by
  constructor
  · intro skill hskill
    have hmonotone : gain cutoff ≤ gain skill := hmono.monotone hskill
    simpa [hroot] using hmonotone
  · intro skill hskill
    have hstrict : gain skill < gain cutoff := hmono hskill
    simpa [hroot] using hstrict.le

/--
The narrow scalar fixed-point step needed for a closed Gaussian cutoff
candidate.  The source-specific work is only to derive continuity and the two
literal-PBO endpoint signs for `boundary`; this theorem supplies the finite
root without assuming a cutoff strategy.
-/
theorem exists_scalarCutoff_of_continuous_boundarySigns
    (boundary : ℝ -> ℝ) (hcontinuous : Continuous boundary)
    {low high : ℝ} (hlowHigh : low < high)
    (hlow : boundary low < 0) (hhigh : 0 < boundary high) :
    ∃ cutoff ∈ Set.Icc low high, boundary cutoff = 0 := by
  have hzero : (0 : ℝ) ∈ Set.Icc (boundary low) (boundary high) :=
    ⟨le_of_lt hlow, le_of_lt hhigh⟩
  rcases (intermediate_value_Icc (le_of_lt hlowHigh)
      hcontinuous.continuousOn hzero) with ⟨cutoff, hcutoff, hroot⟩
  exact ⟨cutoff, hcutoff, hroot⟩

end

end LG21TestOptionalPolicies
