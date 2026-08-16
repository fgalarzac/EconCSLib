import LG21TestOptionalPolicies.PositiveMassPBORefinement

/-!
# Recalibrated positive-mass branch entry

This is the small semantic bridge used at a null public-action branch.  A
candidate is required to have a positive report branch, so its PBO is the
conditional expectation induced by that candidate.  The Definition-1 check is
intentionally scoped to the members of that changed branch, almost everywhere
under its actual candidate law.  It does not assert that every nonmember is
already best responding to the candidate profile.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set

/--
An almost-everywhere Definition-1 check scoped to a specified positive action
branch.  This is independent of the shape of a candidate profile and is the
common semantic form used by literal source-action bridges.
-/
def PositiveMassBranchMembersBestRespond
    {Ω Candidate : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (branch : Set Ω) (candidate : Candidate)
    (memberBestResponse : Candidate -> Ω -> Prop) : Prop :=
  ∀ᵐ omega ∂μ.restrict branch, memberBestResponse candidate omega

namespace PositiveMassPBOCandidateProfile

variable
    {Ω ReportInfo NoReportInfo : Type*}
    [MeasurableSpace Ω] [MeasurableSpace ReportInfo]
    [MeasurableSpace NoReportInfo]
    {μ : Measure Ω} [IsFiniteMeasure μ] {skill : Ω → ℝ}

/--
The Definition-1 predicate for the members of a candidate's changed report
branch.  The restriction is deliberate: positive-mass entry tests the changed
branch after its PBO is recalibrated, while it does not assume a full
whole-population equilibrium for the candidate.
-/
def CandidateReportBranchMembersBestRespond
    (P : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := μ) (skill := skill))
    (memberBestResponse :
      Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
        (μ := μ) (skill := skill) → Ω → Prop) : Prop :=
  PositiveMassBranchMembersBestRespond μ P.reportBranch P memberBestResponse

/--
A candidate positive-mass report entry with its branch-member response check.
PBO calibration is not an extra field: it follows from the candidate carrier
whenever `reportMass_positive` holds.
-/
structure RecalibratedPositiveReportEntry
    (P : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := μ) (skill := skill))
    (memberBestResponse :
      Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
        (μ := μ) (skill := skill) → Ω → Prop) : Prop where
  reportMass_positive : 0 < P.reportMass
  members_best_respond : CandidateReportBranchMembersBestRespond P memberBestResponse

/-- A positive entry supplies the candidate's literal report-branch PBO. -/
theorem RecalibratedPositiveReportEntry.reportPBO
    {P : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := μ) (skill := skill)}
    {memberBestResponse :
      Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
        (μ := μ) (skill := skill) → Ω → Prop}
    (hentry : RecalibratedPositiveReportEntry P memberBestResponse) :
    Integrable skill (μ.restrict P.reportBranch) ∧
      (fun omega => P.reportPBO.estimate (P.reportObservation omega)) =ᵐ[
        μ.restrict P.reportBranch]
        (μ.restrict P.reportBranch)[skill |
          MeasurableSpace.comap P.reportObservation inferInstance] := by
  exact P.reportPBO_consistent_if_positive hentry.reportMass_positive

/--
At a null report branch, this one-directional active-entry witness consists
of a feasible candidate and a recalibrated positive branch whose own members
pass the supplied Definition-1 predicate. It is not a whole-profile
equilibrium witness: a source closeout additionally needs candidate-wide
outsider closure.
-/
def NullReportBranchHasRecalibratedMemberEntry
    (current : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := μ) (skill := skill))
    (canEnter :
      Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
        (μ := μ) (skill := skill) →
      Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
        (μ := μ) (skill := skill) → Prop)
    (memberBestResponse :
      Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
        (μ := μ) (skill := skill) → Ω → Prop) : Prop :=
  current.reportMass = 0 →
    ∃ candidate,
      canEnter current candidate ∧
        RecalibratedPositiveReportEntry candidate memberBestResponse

/-- Stability excludes precisely the recalibrated positive branch entries. -/
def NullReportBranchStableAgainstRecalibratedMemberEntry
    (current : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := μ) (skill := skill))
    (canEnter :
      Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
        (μ := μ) (skill := skill) →
      Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
        (μ := μ) (skill := skill) → Prop)
    (memberBestResponse :
      Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
        (μ := μ) (skill := skill) → Ω → Prop) : Prop :=
  current.reportMass = 0 →
    ¬ ∃ candidate,
      canEnter current candidate ∧
        RecalibratedPositiveReportEntry candidate memberBestResponse

/-- The pre-existing active-entry interface is exactly this scoped form. -/
theorem nullReportBranchHasActiveEntry_iff_recalibratedMemberEntry
    (current : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := μ) (skill := skill))
    (canEnter :
      Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
        (μ := μ) (skill := skill) →
      Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
        (μ := μ) (skill := skill) → Prop)
    (memberBestResponse :
      Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
        (μ := μ) (skill := skill) → Ω → Prop) :
    NullReportBranchHasActiveEntry current canEnter
      (fun candidate =>
        CandidateReportBranchMembersBestRespond candidate memberBestResponse) ↔
      NullReportBranchHasRecalibratedMemberEntry current canEnter
        memberBestResponse := by
  constructor
  · intro hentry hnull
    rcases hentry hnull with ⟨candidate, hcanEnter, hpositive, hmembers⟩
    exact ⟨candidate, hcanEnter, ⟨hpositive, hmembers⟩⟩
  · intro hentry hnull
    rcases hentry hnull with ⟨candidate, hcanEnter, hcertificate⟩
    exact ⟨candidate, hcanEnter, hcertificate.reportMass_positive,
      hcertificate.members_best_respond⟩

/-- A recalibrated member-entry witness refutes null-branch stability. -/
theorem nullReportBranch_not_stable_of_recalibratedMemberEntry
    (current : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := μ) (skill := skill))
    (canEnter :
      Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
        (μ := μ) (skill := skill) →
      Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
        (μ := μ) (skill := skill) → Prop)
    (memberBestResponse :
      Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
        (μ := μ) (skill := skill) → Ω → Prop)
    (hnull : current.reportMass = 0)
    (hentry : NullReportBranchHasRecalibratedMemberEntry current canEnter
      memberBestResponse) :
    ¬ NullReportBranchStableAgainstRecalibratedMemberEntry current canEnter
      memberBestResponse := by
  intro hstable
  exact hstable hnull (hentry hnull)

end PositiveMassPBOCandidateProfile

end

end LG21TestOptionalPolicies
