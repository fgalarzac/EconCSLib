import LG21TestOptionalPolicies.PositiveMassPBORefinement

/-!
# Two-sided closed candidate profiles with positive-mass PBOs

This module is a protocol-neutral interface for a binary candidate action
profile.  It is deliberately distinct from a whole-population pointwise
equilibrium: a conditional mean is available only on an action branch whose
candidate population has positive mass.  In particular, the interface permits
an all-first-action or all-second-action boundary profile without choosing a
numerical PBO at its null branch.

The source-specific meaning of the two action branches is supplied by
`TwoSidedCandidateProfileAdapter`.  For example, an adapter may identify them
with report/no-report or take/no-take and prove the corresponding feasibility
and timing facts.  The closure predicate itself does not inspect the names or
implementation of those action functions.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set

/--
A conditional-mean certificate for a branch of strictly positive candidate
mass.  The positivity proof is an explicit parameter, so this interface has
no certificate, conditional-mean identity, or prescribed value at a null
branch.
-/
structure PositiveMassBranchPBOCertificate
    {Omega Info : Type*} [MeasurableSpace Omega] [MeasurableSpace Info]
    (mu : Measure Omega) [IsFiniteMeasure mu] (skill : Omega -> ℝ)
    (branch : Set Omega) (observation : Omega -> Info) (estimate : Info -> ℝ)
    (hpositive : 0 < mu branch) : Prop where
  integrable : Integrable skill (mu.restrict branch)
  conditional_mean :
    (fun omega => estimate (observation omega)) =ᵐ[mu.restrict branch]
      (mu.restrict branch)[skill |
        MeasurableSpace.comap observation inferInstance]

namespace PositiveMassPBOCandidateProfile

variable
    {Omega ReportInfo NoReportInfo : Type*}
    [MeasurableSpace Omega] [MeasurableSpace ReportInfo]
    [MeasurableSpace NoReportInfo]
    {mu : Measure Omega} [IsFiniteMeasure mu] {skill : Omega -> ℝ}

/--
The generic source-action adapter for a two-branch candidate profile.

The first pair of fields is where a source bridge supplies its action
feasibility and timing obligations.  The remaining fields give the semantic
action permissions and behavioral comparisons used by a closed profile.  Each
behavioral comparison receives a PBO certificate for the branch it evaluates;
therefore it can only be invoked after that branch's positive mass has been
established.

The carrier labels the Boolean `true` branch "report" and the `false` branch
"no-report".  Those are only binary branch labels here: a source adapter may
identify them with any two timed public actions.
-/
structure TwoSidedCandidateProfileAdapter where
  source_actions_feasible :
    Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := mu) (skill := skill) -> Prop
  source_timing_respected :
    Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := mu) (skill := skill) -> Prop
  report_action_eligible :
    Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := mu) (skill := skill) -> Omega -> Prop
  noReport_action_eligible :
    Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := mu) (skill := skill) -> Omega -> Prop
  report_member_weak_response :
    (P : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := mu) (skill := skill)) ->
    (hpositive : 0 < P.reportMass) ->
    PositiveMassBranchPBOCertificate mu skill P.reportBranch
      P.reportObservation P.reportPBO.estimate hpositive -> Omega -> Prop
  noReport_member_weak_response :
    (P : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := mu) (skill := skill)) ->
    (hpositive : 0 < P.noReportMass) ->
    PositiveMassBranchPBOCertificate mu skill P.noReportBranch
      P.noReportObservation P.noReportPBO.estimate hpositive -> Omega -> Prop
  report_strict_gain :
    (P : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := mu) (skill := skill)) ->
    (hpositive : 0 < P.reportMass) ->
    PositiveMassBranchPBOCertificate mu skill P.reportBranch
      P.reportObservation P.reportPBO.estimate hpositive -> Omega -> Prop
  noReport_strict_gain :
    (P : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := mu) (skill := skill)) ->
    (hpositive : 0 < P.noReportMass) ->
    PositiveMassBranchPBOCertificate mu skill P.noReportBranch
      P.noReportObservation P.noReportPBO.estimate hpositive -> Omega -> Prop

/--
The candidate profile itself provides a report-branch conditional-mean
certificate after, and only after, report-branch positivity is given.
-/
def reportBranchPBOCertificate
    (P : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := mu) (skill := skill))
    (hpositive : 0 < P.reportMass) :
    PositiveMassBranchPBOCertificate mu skill P.reportBranch
      P.reportObservation P.reportPBO.estimate hpositive := by
  rcases P.reportPBO_consistent_if_positive hpositive with ⟨hintegrable, hmean⟩
  exact ⟨hintegrable, hmean⟩

/--
The candidate profile itself provides a no-report-branch conditional-mean
certificate after, and only after, no-report-branch positivity is given.
-/
def noReportBranchPBOCertificate
    (P : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := mu) (skill := skill))
    (hpositive : 0 < P.noReportMass) :
    PositiveMassBranchPBOCertificate mu skill P.noReportBranch
      P.noReportObservation P.noReportPBO.estimate hpositive := by
  rcases P.noReportPBO_consistent_if_positive hpositive with ⟨hintegrable, hmean⟩
  exact ⟨hintegrable, hmean⟩

/--
A source-feasible, source-timed binary candidate profile closed under its own
positive-mass PBOs.

For either branch, all PBO, member-response, and outsider-closure obligations
are quantified over a proof that the branch has positive mass.  Consequently,
at a boundary profile the obligations for the null branch are absent rather
than being discharged with an arbitrary off-path estimate.  A source bridge
that wishes to rule out a positive-mass transition to such a branch must do so
with a separate candidate profile and that candidate's own certificate.
-/
structure TwoSidedPositiveMassClosedCandidateProfile
    (A : TwoSidedCandidateProfileAdapter
      (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (mu := mu) (skill := skill))
    (P : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := mu) (skill := skill)) : Prop where
  source_actions_feasible : A.source_actions_feasible P
  source_timing_respected : A.source_timing_respected P
  report_pbo_if_positive : ∀ hpositive : 0 < P.reportMass,
    PositiveMassBranchPBOCertificate mu skill P.reportBranch
      P.reportObservation P.reportPBO.estimate hpositive
  noReport_pbo_if_positive : ∀ hpositive : 0 < P.noReportMass,
    PositiveMassBranchPBOCertificate mu skill P.noReportBranch
      P.noReportObservation P.noReportPBO.estimate hpositive
  report_members_eligible_if_positive : ∀ hpositive : 0 < P.reportMass,
    ∀ᵐ omega ∂mu.restrict P.reportBranch, A.report_action_eligible P omega
  noReport_members_eligible_if_positive : ∀ hpositive : 0 < P.noReportMass,
    ∀ᵐ omega ∂mu.restrict P.noReportBranch, A.noReport_action_eligible P omega
  report_members_weakly_respond_if_positive : ∀ hpositive : 0 < P.reportMass,
    ∀ᵐ omega ∂mu.restrict P.reportBranch,
      A.report_member_weak_response P hpositive
        (report_pbo_if_positive hpositive) omega
  noReport_members_weakly_respond_if_positive :
    ∀ hpositive : 0 < P.noReportMass,
      ∀ᵐ omega ∂mu.restrict P.noReportBranch,
        A.noReport_member_weak_response P hpositive
          (noReport_pbo_if_positive hpositive) omega
  /-- Every eligible outsider to a positive report branch lacks a strict gain
  from that branch under the candidate's own positive-branch PBO. -/
  report_outsiders_closed_under_strict_gain_if_positive :
    ∀ hpositive : 0 < P.reportMass,
      ∀ᵐ omega ∂mu.restrict
        {omega | A.report_action_eligible P omega ∧ omega ∉ P.reportBranch},
        ¬ A.report_strict_gain P hpositive (report_pbo_if_positive hpositive) omega
  /-- Every eligible outsider to a positive no-report branch lacks a strict
  gain from that branch under the candidate's own positive-branch PBO. -/
  noReport_outsiders_closed_under_strict_gain_if_positive :
    ∀ hpositive : 0 < P.noReportMass,
      ∀ᵐ omega ∂mu.restrict
        {omega | A.noReport_action_eligible P omega ∧ omega ∉ P.noReportBranch},
        ¬ A.noReport_strict_gain P hpositive
          (noReport_pbo_if_positive hpositive) omega

namespace TwoSidedPositiveMassClosedCandidateProfile

/-- Project the report-branch PBO only with an explicit positive-mass proof. -/
theorem report_pbo
    {A : TwoSidedCandidateProfileAdapter
      (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (mu := mu) (skill := skill)}
    {P : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := mu) (skill := skill)}
    (H : TwoSidedPositiveMassClosedCandidateProfile A P)
    (hpositive : 0 < P.reportMass) :
    PositiveMassBranchPBOCertificate mu skill P.reportBranch
      P.reportObservation P.reportPBO.estimate hpositive :=
  H.report_pbo_if_positive hpositive

/-- Project the no-report-branch PBO only with an explicit positive-mass proof. -/
theorem noReport_pbo
    {A : TwoSidedCandidateProfileAdapter
      (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (mu := mu) (skill := skill)}
    {P : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := mu) (skill := skill)}
    (H : TwoSidedPositiveMassClosedCandidateProfile A P)
    (hpositive : 0 < P.noReportMass) :
    PositiveMassBranchPBOCertificate mu skill P.noReportBranch
      P.noReportObservation P.noReportPBO.estimate hpositive :=
  H.noReport_pbo_if_positive hpositive

/-- The report-branch member response is exposed only after report positivity. -/
theorem report_members_weakly_respond
    {A : TwoSidedCandidateProfileAdapter
      (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (mu := mu) (skill := skill)}
    {P : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := mu) (skill := skill)}
    (H : TwoSidedPositiveMassClosedCandidateProfile A P)
    (hpositive : 0 < P.reportMass) :
    ∀ᵐ omega ∂mu.restrict P.reportBranch,
      A.report_member_weak_response P hpositive (H.report_pbo hpositive) omega :=
  H.report_members_weakly_respond_if_positive hpositive

/-- The no-report member response is exposed only after no-report positivity. -/
theorem noReport_members_weakly_respond
    {A : TwoSidedCandidateProfileAdapter
      (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (mu := mu) (skill := skill)}
    {P : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := mu) (skill := skill)}
    (H : TwoSidedPositiveMassClosedCandidateProfile A P)
    (hpositive : 0 < P.noReportMass) :
    ∀ᵐ omega ∂mu.restrict P.noReportBranch,
      A.noReport_member_weak_response P hpositive (H.noReport_pbo hpositive) omega :=
  H.noReport_members_weakly_respond_if_positive hpositive

/-- Positive report-branch outsiders are closed against strict gain. -/
theorem report_outsiders_closed_under_strict_gain
    {A : TwoSidedCandidateProfileAdapter
      (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (mu := mu) (skill := skill)}
    {P : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := mu) (skill := skill)}
    (H : TwoSidedPositiveMassClosedCandidateProfile A P)
    (hpositive : 0 < P.reportMass) :
    ∀ᵐ omega ∂mu.restrict
      {omega | A.report_action_eligible P omega ∧ omega ∉ P.reportBranch},
      ¬ A.report_strict_gain P hpositive (H.report_pbo hpositive) omega :=
  H.report_outsiders_closed_under_strict_gain_if_positive hpositive

/-- Positive no-report-branch outsiders are closed against strict gain. -/
theorem noReport_outsiders_closed_under_strict_gain
    {A : TwoSidedCandidateProfileAdapter
      (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (mu := mu) (skill := skill)}
    {P : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := mu) (skill := skill)}
    (H : TwoSidedPositiveMassClosedCandidateProfile A P)
    (hpositive : 0 < P.noReportMass) :
    ∀ᵐ omega ∂mu.restrict
      {omega | A.noReport_action_eligible P omega ∧ omega ∉ P.noReportBranch},
      ¬ A.noReport_strict_gain P hpositive (H.noReport_pbo hpositive) omega :=
  H.noReport_outsiders_closed_under_strict_gain_if_positive hpositive

end TwoSidedPositiveMassClosedCandidateProfile

end PositiveMassPBOCandidateProfile

end

end LG21TestOptionalPolicies
