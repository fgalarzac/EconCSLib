import DGJ24OptimalStrategiesRCV.MainTheorems

/-!
# SmartAllocation Source Model

This file contains a source-shaped constructor for Theorem 3.1's
SmartAllocation proof.  The core optimization theorem in `MainTheorems.lean`
already proves that exact componentwise slack filling is optimal.  What remains
paper-specific is the Algorithm 3 decomposition of strategic additions into
net-new first-use slack units.

The model below packages that decomposition in the form needed by the checked
slack-filling theorem.  A later STV state-machine proof should instantiate this
record from the concrete round dynamics, tie-breaking, availability, and
no-new-slack induction in the source proof.
-/

namespace DGJ24OptimalStrategiesRCV

open scoped BigOperators
open EconCSLib.SocialChoice.Voting

/--
Source-shaped first-use slack model for Algorithm 3.

`requiredSlack` is the net-new slack that must be created at each independent
round-local component after all reusable available votes have been accounted
for.  `firstUse` maps an arbitrary feasible strategic addition to the number of
added votes whose first effective use pays for each slack component.  The model
fields are exactly the paper proof obligations: exact filling is feasible, every
feasible addition fills every required first-use slot, and the objective is the
sum of first-use slots.
-/
structure SmartAllocationFirstUseSlackModel
    (Addition Slack : Type*) [Fintype Slack] where
  requiredSlack :
    SmartAllocationProblem Addition → Slack → ℕ
  firstUse :
    SmartAllocationProblem Addition → Addition → Slack → ℕ
  additionOf :
    SmartAllocationProblem Addition → (Slack → ℕ) → Addition
  feasible_of_slack_feasible :
    ∀ (problem : SmartAllocationProblem Addition) (allocation : Slack → ℕ),
      (∀ slack, requiredSlack problem slack ≤ allocation slack) →
        problem.feasible (additionOf problem allocation)
  firstUse_feasible_of_feasible :
    ∀ (problem : SmartAllocationProblem Addition) (addition : Addition),
      problem.feasible addition →
        ∀ slack, requiredSlack problem slack ≤ firstUse problem addition slack
  cost_exact_fill_eq :
    ∀ problem : SmartAllocationProblem Addition,
      problem.cost
          (additionOf problem (fun slack => requiredSlack problem slack)) =
        ∑ slack, (requiredSlack problem slack : ℝ)
  cost_eq_firstUse_of_feasible :
    ∀ (problem : SmartAllocationProblem Addition) (addition : Addition),
      problem.feasible addition →
        problem.cost addition =
          ∑ slack, (firstUse problem addition slack : ℝ)

namespace SmartAllocationFirstUseSlackModel

/-- The componentwise slack-filling instance induced by a first-use model. -/
def slackProblem {Addition Slack : Type*} [Fintype Slack]
    (model : SmartAllocationFirstUseSlackModel Addition Slack)
    (problem : SmartAllocationProblem Addition) :
    SmartAllocationSlackFillingProblem Slack where
  requiredSlack := model.requiredSlack problem
  budget := problem.budget
  uniqueBallotCount := problem.uniqueBallotCount
  candidateCount := problem.candidateCount

/-- The slack allocation induced by an arbitrary strategic addition. -/
def slackOf {Addition Slack : Type*} [Fintype Slack]
    (model : SmartAllocationFirstUseSlackModel Addition Slack)
    (problem : SmartAllocationProblem Addition) (addition : Addition) :
    Slack → ℕ :=
  model.firstUse problem addition

/--
The first-use source model supplies the concrete SmartAllocation slack
reduction certificate used by Theorem 3.1.
-/
theorem concreteSlackReduction_optimal_and_linear_runtime
    {Addition Slack : Type*} [Fintype Slack]
    (model : SmartAllocationFirstUseSlackModel Addition Slack)
    (problem : SmartAllocationProblem Addition) :
    EconCSLib.Optimization.IsMinimizerOn
        problem.feasible problem.cost
        (smartAllocationSlackReductionAlgorithm model.slackProblem
          model.additionOf problem) ∧
      smartAllocationSlackReductionOperationCount problem ≤
        SmartAllocationProblem.linearRuntimeBound problem := by
  exact
    theorem3_1_smartAllocation_concreteSlackReductionAlgorithm_optimal_and_linear_runtime
      (slackProblem := model.slackProblem)
      (slackOf := model.slackOf)
      (additionOf := model.additionOf)
      (by
        intro currentProblem allocation hallocation
        exact model.feasible_of_slack_feasible currentProblem allocation
          hallocation)
      (by
        intro currentProblem addition hfeasible
        exact model.firstUse_feasible_of_feasible currentProblem addition
          hfeasible)
      (by
        intro currentProblem
        simpa [smartAllocationSlackReductionAlgorithm,
          SmartAllocationSlackFillingProblem.algorithm,
          SmartAllocationSlackFillingProblem.cost, slackProblem] using
          model.cost_exact_fill_eq currentProblem)
      (by
        intro currentProblem addition hfeasible
        simpa [SmartAllocationSlackFillingProblem.cost, slackOf,
          slackProblem] using
          model.cost_eq_firstUse_of_feasible currentProblem addition
            hfeasible)
      problem

end SmartAllocationFirstUseSlackModel

/--
Algorithm 3 first-use decomposition certificate.

The source proof argues that, when the allocation rule converges without
creating new earlier slacks, each feasible strategic addition can be partitioned
by the first round-local component where the added vote is effectively used.
This certificate names the source obligations before they are repackaged as the
generic first-use slack model.
-/
structure Algorithm3FirstUseSlackCertificate
    (Addition Slack : Type*) [Fintype Slack] where
  requiredSlack :
    SmartAllocationProblem Addition → Slack → ℕ
  firstUse :
    SmartAllocationProblem Addition → Addition → Slack → ℕ
  exactFillAddition :
    SmartAllocationProblem Addition → (Slack → ℕ) → Addition
  exact_fill_feasible :
    ∀ (problem : SmartAllocationProblem Addition) (allocation : Slack → ℕ),
      (∀ slack, requiredSlack problem slack ≤ allocation slack) →
        problem.feasible (exactFillAddition problem allocation)
  feasible_addition_fills_required_first_use :
    ∀ (problem : SmartAllocationProblem Addition) (addition : Addition),
      problem.feasible addition →
        ∀ slack, requiredSlack problem slack ≤ firstUse problem addition slack
  exact_fill_cost_eq_required_slack_sum :
    ∀ problem : SmartAllocationProblem Addition,
      problem.cost
          (exactFillAddition problem (fun slack => requiredSlack problem slack)) =
        ∑ slack, (requiredSlack problem slack : ℝ)
  feasible_addition_cost_eq_first_use_sum :
    ∀ (problem : SmartAllocationProblem Addition) (addition : Addition),
      problem.feasible addition →
        problem.cost addition =
          ∑ slack, (firstUse problem addition slack : ℝ)

namespace Algorithm3FirstUseSlackCertificate

/--
The Algorithm 3 first-use certificate is exactly the source-shaped instance of
the generic first-use slack model used by the checked optimization theorem.
-/
def toFirstUseSlackModel {Addition Slack : Type*} [Fintype Slack]
    (cert : Algorithm3FirstUseSlackCertificate Addition Slack) :
    SmartAllocationFirstUseSlackModel Addition Slack where
  requiredSlack := cert.requiredSlack
  firstUse := cert.firstUse
  additionOf := cert.exactFillAddition
  feasible_of_slack_feasible := cert.exact_fill_feasible
  firstUse_feasible_of_feasible :=
    cert.feasible_addition_fills_required_first_use
  cost_exact_fill_eq := cert.exact_fill_cost_eq_required_slack_sum
  cost_eq_firstUse_of_feasible :=
    cert.feasible_addition_cost_eq_first_use_sum

/--
Theorem 3.1 route from the source Algorithm 3 first-use decomposition: once the
paper's no-new-slack/first-use decomposition is checked, the existing
componentwise slack-filling theorem proves optimality and the claimed linear
operation bound.
-/
theorem concreteSlackReduction_optimal_and_linear_runtime
    {Addition Slack : Type*} [Fintype Slack]
    (cert : Algorithm3FirstUseSlackCertificate Addition Slack)
    (problem : SmartAllocationProblem Addition) :
    EconCSLib.Optimization.IsMinimizerOn
        problem.feasible problem.cost
        (smartAllocationSlackReductionAlgorithm
          cert.toFirstUseSlackModel.slackProblem
          cert.toFirstUseSlackModel.additionOf problem) ∧
      smartAllocationSlackReductionOperationCount problem ≤
        SmartAllocationProblem.linearRuntimeBound problem :=
  cert.toFirstUseSlackModel.concreteSlackReduction_optimal_and_linear_runtime
    problem

end Algorithm3FirstUseSlackCertificate

/--
Algorithm 3 first-use decomposition certificate for one concrete
SmartAllocation instance.

This avoids requiring a source proof to build a uniform certificate for every
`SmartAllocationProblem Addition` when the paper argument has already fixed the
target structure and its support-count data.
-/
structure Algorithm3ProblemFirstUseSlackCertificate
    (Addition Slack : Type*) [Fintype Slack]
    (problem : SmartAllocationProblem Addition) where
  requiredSlack : Slack → ℕ
  firstUse : Addition → Slack → ℕ
  exactFillAddition : (Slack → ℕ) → Addition
  exact_fill_feasible :
    ∀ allocation : Slack → ℕ,
      (∀ slack, requiredSlack slack ≤ allocation slack) →
        problem.feasible (exactFillAddition allocation)
  feasible_addition_fills_required_first_use :
    ∀ addition : Addition,
      problem.feasible addition →
        ∀ slack, requiredSlack slack ≤ firstUse addition slack
  exact_fill_cost_eq_required_slack_sum :
    problem.cost
        (exactFillAddition (fun slack => requiredSlack slack)) =
      ∑ slack, (requiredSlack slack : ℝ)
  feasible_addition_cost_eq_first_use_sum :
    ∀ addition : Addition,
      problem.feasible addition →
        problem.cost addition =
          ∑ slack, (firstUse addition slack : ℝ)

namespace Algorithm3ProblemFirstUseSlackCertificate

/-- The componentwise slack-filling instance for a fixed-problem certificate. -/
def slackProblem {Addition Slack : Type*} [Fintype Slack]
    {problem : SmartAllocationProblem Addition}
    (cert :
      Algorithm3ProblemFirstUseSlackCertificate Addition Slack problem) :
    SmartAllocationSlackFillingProblem Slack where
  requiredSlack := cert.requiredSlack
  budget := problem.budget
  uniqueBallotCount := problem.uniqueBallotCount
  candidateCount := problem.candidateCount

/-- The exact-fill addition selected by the fixed-problem Algorithm 3 certificate. -/
def exactFill {Addition Slack : Type*} [Fintype Slack]
    {problem : SmartAllocationProblem Addition}
    (cert :
      Algorithm3ProblemFirstUseSlackCertificate Addition Slack problem) :
    Addition :=
  cert.exactFillAddition (fun slack => cert.requiredSlack slack)

/--
Fixed-problem Theorem 3.1 route from the Algorithm 3 first-use decomposition.
Only the obligations for the concrete `problem` are required.
-/
theorem exactFill_optimal_and_linear_runtime
    {Addition Slack : Type*} [Fintype Slack]
    {problem : SmartAllocationProblem Addition}
    (cert :
      Algorithm3ProblemFirstUseSlackCertificate Addition Slack problem) :
    EconCSLib.Optimization.IsMinimizerOn
        problem.feasible problem.cost cert.exactFill ∧
      smartAllocationSlackReductionOperationCount problem ≤
        SmartAllocationProblem.linearRuntimeBound problem := by
  refine ⟨?_, le_rfl⟩
  refine ⟨?_, ?_⟩
  · exact cert.exact_fill_feasible
      (fun slack => cert.requiredSlack slack) (fun _ => le_rfl)
  · intro addition haddition
    have hslackMin :=
      SmartAllocationSlackFillingProblem.algorithm_optimal cert.slackProblem
    have hslackFeasible :
        SmartAllocationSlackFillingProblem.feasible cert.slackProblem
          (cert.firstUse addition) := by
      intro slack
      exact cert.feasible_addition_fills_required_first_use addition
        haddition slack
    calc
      problem.cost cert.exactFill
          = SmartAllocationSlackFillingProblem.cost cert.slackProblem
              (SmartAllocationSlackFillingProblem.algorithm
                cert.slackProblem) := by
            simpa [exactFill, slackProblem,
              SmartAllocationSlackFillingProblem.algorithm,
              SmartAllocationSlackFillingProblem.cost] using
              cert.exact_fill_cost_eq_required_slack_sum
      _ ≤ SmartAllocationSlackFillingProblem.cost cert.slackProblem
            (cert.firstUse addition) :=
          hslackMin.le hslackFeasible
      _ = problem.cost addition := by
            simpa [slackProblem, SmartAllocationSlackFillingProblem.cost] using
              (cert.feasible_addition_cost_eq_first_use_sum addition
                haddition).symm

end Algorithm3ProblemFirstUseSlackCertificate

/--
Relevant active-support count vector for ballot-valued SmartAllocation
instances.  The source Algorithm A/SmartAllocation models only inspect
active-support counts at the active sets that occur in the target trace.
-/
def relevantActiveSupportCounts {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter)
    (relevantActiveSets : Finset (Finset Candidate))
    (addition : Voter → RCVBallot Candidate) :
    (active : Finset Candidate) → active ∈ relevantActiveSets →
      Candidate → ℕ :=
  fun active _hactive candidate =>
    (Ballot.activeSupport voters addition active candidate).card

/--
Source-shaped support-count model for ballot-valued SmartAllocation problems.
It records the concrete source convention that feasibility and objective value
are functions of the relevant active-support counts, rather than of irrelevant
suffixes, prefixes, or exhausted-ballot completions.
-/
structure SmartAllocationSupportCountModel
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (problem :
      SmartAllocationProblem (Voter → RCVBallot Candidate))
    (voters : Finset Voter)
    (relevantActiveSets : Finset (Finset Candidate)) where
  feasibleCounts :
    ((active : Finset Candidate) → active ∈ relevantActiveSets →
      Candidate → ℕ) → Prop
  costCounts :
    ((active : Finset Candidate) → active ∈ relevantActiveSets →
      Candidate → ℕ) → ℝ
  feasible_iff :
    ∀ addition, problem.feasible addition ↔
      feasibleCounts
        (relevantActiveSupportCounts voters relevantActiveSets addition)
  cost_eq :
    ∀ addition, problem.cost addition =
      costCounts
        (relevantActiveSupportCounts voters relevantActiveSets addition)

namespace SmartAllocationSupportCountModel

/--
Support-count equality preserves feasibility for a concrete support-count
SmartAllocation source model.
-/
theorem feasible_of_support_counts_eq
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {problem :
      SmartAllocationProblem (Voter → RCVBallot Candidate)}
    {voters : Finset Voter}
    {relevantActiveSets : Finset (Finset Candidate)}
    (model :
      SmartAllocationSupportCountModel problem voters relevantActiveSets)
    {base robust : Voter → RCVBallot Candidate}
    (hbase : problem.feasible base)
    (hcounts :
      ∀ active, active ∈ relevantActiveSets → ∀ candidate,
        (Ballot.activeSupport voters robust active candidate).card =
          (Ballot.activeSupport voters base active candidate).card) :
    problem.feasible robust := by
  have hbaseCounts :
      model.feasibleCounts
        (relevantActiveSupportCounts voters relevantActiveSets base) :=
    (model.feasible_iff base).1 hbase
  have hcountVector :
      relevantActiveSupportCounts voters relevantActiveSets robust =
        relevantActiveSupportCounts voters relevantActiveSets base := by
    funext active hactive candidate
    exact hcounts active hactive candidate
  exact (model.feasible_iff robust).2 (by
    simpa [hcountVector] using hbaseCounts)

/--
Support-count equality preserves objective value for a concrete support-count
SmartAllocation source model.
-/
theorem cost_eq_of_support_counts_eq
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {problem :
      SmartAllocationProblem (Voter → RCVBallot Candidate)}
    {voters : Finset Voter}
    {relevantActiveSets : Finset (Finset Candidate)}
    (model :
      SmartAllocationSupportCountModel problem voters relevantActiveSets)
    {base robust : Voter → RCVBallot Candidate}
    (hcounts :
      ∀ active, active ∈ relevantActiveSets → ∀ candidate,
        (Ballot.activeSupport voters robust active candidate).card =
          (Ballot.activeSupport voters base active candidate).card) :
    problem.cost robust = problem.cost base := by
  have hcountVector :
      relevantActiveSupportCounts voters relevantActiveSets robust =
        relevantActiveSupportCounts voters relevantActiveSets base := by
    funext active hactive candidate
    exact hcounts active hactive candidate
  rw [model.cost_eq robust, model.cost_eq base, hcountVector]

end SmartAllocationSupportCountModel

/--
Concrete ballot-valued SmartAllocation instances whose feasibility and cost are
defined from the relevant active-support counts.  This is the source-shaped
problem type for DGJ24 Algorithm 3 and the DGJ26 robust-output reuse: once a
candidate active set has been fixed by the target trace, ballot details outside
these active-support counts cannot affect feasibility or objective value.
-/
structure SupportCountSmartAllocationData
    (Voter Candidate : Type*) [DecidableEq Candidate] where
  voters : Finset Voter
  relevantActiveSets : Finset (Finset Candidate)
  feasibleCounts :
    ((active : Finset Candidate) → active ∈ relevantActiveSets →
      Candidate → ℕ) → Prop
  costCounts :
    ((active : Finset Candidate) → active ∈ relevantActiveSets →
      Candidate → ℕ) → ℝ
  budget : ℕ
  uniqueBallotCount : ℕ
  candidateCount : ℕ

namespace SupportCountSmartAllocationData

/-- The concrete `SmartAllocationProblem` induced by support-count data. -/
def problem {Voter Candidate : Type*} [DecidableEq Candidate]
    (data : SupportCountSmartAllocationData Voter Candidate) :
    SmartAllocationProblem (Voter → RCVBallot Candidate) where
  feasible addition :=
    data.feasibleCounts
      (relevantActiveSupportCounts data.voters data.relevantActiveSets
        addition)
  cost addition :=
    data.costCounts
      (relevantActiveSupportCounts data.voters data.relevantActiveSets
        addition)
  budget := data.budget
  uniqueBallotCount := data.uniqueBallotCount
  candidateCount := data.candidateCount

/--
The support-count source model for a concrete support-count SmartAllocation
instance is immediate by unfolding the problem definition.
-/
def supportCountModel {Voter Candidate : Type*} [DecidableEq Candidate]
    (data : SupportCountSmartAllocationData Voter Candidate) :
    SmartAllocationSupportCountModel data.problem data.voters
      data.relevantActiveSets where
  feasibleCounts := data.feasibleCounts
  costCounts := data.costCounts
  feasible_iff := by
    intro addition
    rfl
  cost_eq := by
    intro addition
    rfl

/--
Build a fixed-problem Algorithm 3 first-use certificate from primitive
support-count obligations for the concrete support-count SmartAllocation data.
-/
def algorithm3ProblemFirstUseSlackCertificate
    {Voter Candidate Slack : Type*} [DecidableEq Candidate] [Fintype Slack]
    (data : SupportCountSmartAllocationData Voter Candidate)
    (requiredSlack : Slack → ℕ)
    (firstUse : (Voter → RCVBallot Candidate) → Slack → ℕ)
    (exactFillAddition : (Slack → ℕ) → Voter → RCVBallot Candidate)
    (exact_fill_feasible_counts :
      ∀ allocation : Slack → ℕ,
        (∀ slack, requiredSlack slack ≤ allocation slack) →
          data.feasibleCounts
            (relevantActiveSupportCounts data.voters data.relevantActiveSets
              (exactFillAddition allocation)))
    (feasible_addition_fills_required_first_use :
      ∀ addition : Voter → RCVBallot Candidate,
        data.feasibleCounts
            (relevantActiveSupportCounts data.voters data.relevantActiveSets
              addition) →
          ∀ slack, requiredSlack slack ≤ firstUse addition slack)
    (exact_fill_cost_counts_eq_required_slack_sum :
      data.costCounts
          (relevantActiveSupportCounts data.voters data.relevantActiveSets
            (exactFillAddition (fun slack => requiredSlack slack))) =
        ∑ slack, (requiredSlack slack : ℝ))
    (feasible_addition_cost_counts_eq_first_use_sum :
      ∀ addition : Voter → RCVBallot Candidate,
        data.feasibleCounts
            (relevantActiveSupportCounts data.voters data.relevantActiveSets
              addition) →
          data.costCounts
              (relevantActiveSupportCounts data.voters data.relevantActiveSets
                addition) =
            ∑ slack, (firstUse addition slack : ℝ)) :
    Algorithm3ProblemFirstUseSlackCertificate
      (Voter → RCVBallot Candidate) Slack data.problem where
  requiredSlack := requiredSlack
  firstUse := firstUse
  exactFillAddition := exactFillAddition
  exact_fill_feasible := by
    intro allocation hallocation
    exact exact_fill_feasible_counts allocation hallocation
  feasible_addition_fills_required_first_use := by
    intro addition hfeasible
    exact feasible_addition_fills_required_first_use addition hfeasible
  exact_fill_cost_eq_required_slack_sum := by
    exact exact_fill_cost_counts_eq_required_slack_sum
  feasible_addition_cost_eq_first_use_sum := by
    intro addition hfeasible
    exact feasible_addition_cost_counts_eq_first_use_sum addition hfeasible

/--
Support-count equality preserves feasibility for concrete support-count
SmartAllocation data.
-/
theorem feasible_of_support_counts_eq
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (data : SupportCountSmartAllocationData Voter Candidate)
    {base robust : Voter → RCVBallot Candidate}
    (hbase : data.problem.feasible base)
    (hcounts :
      ∀ active, active ∈ data.relevantActiveSets → ∀ candidate,
        (Ballot.activeSupport data.voters robust active candidate).card =
          (Ballot.activeSupport data.voters base active candidate).card) :
    data.problem.feasible robust :=
  SmartAllocationSupportCountModel.feasible_of_support_counts_eq
    (data.supportCountModel) hbase hcounts

/--
Support-count equality preserves objective value for concrete support-count
SmartAllocation data.
-/
theorem cost_eq_of_support_counts_eq
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (data : SupportCountSmartAllocationData Voter Candidate)
    {base robust : Voter → RCVBallot Candidate}
    (hcounts :
      ∀ active, active ∈ data.relevantActiveSets → ∀ candidate,
        (Ballot.activeSupport data.voters robust active candidate).card =
          (Ballot.activeSupport data.voters base active candidate).card) :
    data.problem.cost robust = data.problem.cost base :=
  SmartAllocationSupportCountModel.cost_eq_of_support_counts_eq
    (data.supportCountModel) hcounts

end SupportCountSmartAllocationData

/--
Concrete support-count semantics for Algorithm 3's one-pass allocation loop.

The paper's loop processes the target rounds in order, reusing available votes
before creating net-new first-use slack.  This record makes that source
convention explicit at the support-count level: feasibility means every
round-local first-use component reaches its required slack, and the objective
is the total first-use mass.  The only algorithm-specific realization fact is
that the exact-fill addition produced by the loop realizes the requested
first-use counts exactly.
-/
structure Algorithm3SupportCountLoopData
    (Voter Candidate Slack : Type*) [DecidableEq Candidate]
    [Fintype Slack] where
  voters : Finset Voter
  relevantActiveSets : Finset (Finset Candidate)
  requiredSlack : Slack → ℕ
  firstUseCounts :
    ((active : Finset Candidate) → active ∈ relevantActiveSets →
      Candidate → ℕ) → Slack → ℕ
  exactFillAddition : (Slack → ℕ) → Voter → RCVBallot Candidate
  exactFill_firstUseCounts_eq :
    ∀ allocation slack,
      firstUseCounts
          (relevantActiveSupportCounts voters relevantActiveSets
            (exactFillAddition allocation)) slack =
        allocation slack
  budget : ℕ
  uniqueBallotCount : ℕ
  candidateCount : ℕ

namespace Algorithm3SupportCountLoopData

/-- Feasibility generated by Algorithm 3 first-use support counts. -/
def feasibleCounts {Voter Candidate Slack : Type*} [DecidableEq Candidate]
    [Fintype Slack]
    (data : Algorithm3SupportCountLoopData Voter Candidate Slack)
    (counts :
      (active : Finset Candidate) → active ∈ data.relevantActiveSets →
        Candidate → ℕ) : Prop :=
  ∀ slack, data.requiredSlack slack ≤ data.firstUseCounts counts slack

/-- Objective generated by Algorithm 3 first-use support counts. -/
def costCounts {Voter Candidate Slack : Type*} [DecidableEq Candidate]
    [Fintype Slack]
    (data : Algorithm3SupportCountLoopData Voter Candidate Slack)
    (counts :
      (active : Finset Candidate) → active ∈ data.relevantActiveSets →
        Candidate → ℕ) : ℝ :=
  ∑ slack, (data.firstUseCounts counts slack : ℝ)

/--
The support-count SmartAllocation data induced by concrete Algorithm 3
first-use semantics.
-/
def supportCountData {Voter Candidate Slack : Type*} [DecidableEq Candidate]
    [Fintype Slack]
    (data : Algorithm3SupportCountLoopData Voter Candidate Slack) :
    SupportCountSmartAllocationData Voter Candidate where
  voters := data.voters
  relevantActiveSets := data.relevantActiveSets
  feasibleCounts := data.feasibleCounts
  costCounts := data.costCounts
  budget := data.budget
  uniqueBallotCount := data.uniqueBallotCount
  candidateCount := data.candidateCount

/-- The SmartAllocation problem generated by Algorithm 3 first-use semantics. -/
def problem {Voter Candidate Slack : Type*} [DecidableEq Candidate]
    [Fintype Slack]
    (data : Algorithm3SupportCountLoopData Voter Candidate Slack) :
    SmartAllocationProblem (Voter → RCVBallot Candidate) :=
  data.supportCountData.problem

/-- First-use counts assigned to a concrete strategic addition. -/
def firstUse {Voter Candidate Slack : Type*} [DecidableEq Candidate]
    [Fintype Slack]
    (data : Algorithm3SupportCountLoopData Voter Candidate Slack)
    (addition : Voter → RCVBallot Candidate) : Slack → ℕ :=
  data.firstUseCounts
    (relevantActiveSupportCounts data.voters data.relevantActiveSets addition)

/-- Algorithm 3 exact-fill output for the required first-use slacks. -/
def exactFill {Voter Candidate Slack : Type*} [DecidableEq Candidate]
    [Fintype Slack]
    (data : Algorithm3SupportCountLoopData Voter Candidate Slack) :
    Voter → RCVBallot Candidate :=
  data.exactFillAddition data.requiredSlack

/--
Concrete Algorithm 3 first-use semantics instantiate the fixed-problem
first-use certificate used by the checked componentwise slack theorem.
-/
def problemFirstUseSlackCertificate
    {Voter Candidate Slack : Type*} [DecidableEq Candidate] [Fintype Slack]
    (data : Algorithm3SupportCountLoopData Voter Candidate Slack) :
    Algorithm3ProblemFirstUseSlackCertificate
      (Voter → RCVBallot Candidate) Slack data.problem where
  requiredSlack := data.requiredSlack
  firstUse := data.firstUse
  exactFillAddition := data.exactFillAddition
  exact_fill_feasible := by
    intro allocation hallocation slack
    change
      data.requiredSlack slack ≤
        data.firstUseCounts
          (relevantActiveSupportCounts data.voters data.relevantActiveSets
            (data.exactFillAddition allocation)) slack
    rw [data.exactFill_firstUseCounts_eq allocation slack]
    exact hallocation slack
  feasible_addition_fills_required_first_use := by
    intro addition hfeasible slack
    simpa [problem, supportCountData, SupportCountSmartAllocationData.problem,
      feasibleCounts, firstUse] using
      (hfeasible slack)
  exact_fill_cost_eq_required_slack_sum := by
    simp [problem, supportCountData, SupportCountSmartAllocationData.problem,
      costCounts, data.exactFill_firstUseCounts_eq]
  feasible_addition_cost_eq_first_use_sum := by
    intro addition _hfeasible
    rfl

/--
Algorithm 3's concrete support-count loop proves optimality and the exact
`m * n` operation bound for its generated SmartAllocation problem.
-/
theorem exactFill_optimal_and_linear_runtime
    {Voter Candidate Slack : Type*} [DecidableEq Candidate] [Fintype Slack]
    (data : Algorithm3SupportCountLoopData Voter Candidate Slack) :
    EconCSLib.Optimization.IsMinimizerOn
        data.problem.feasible data.problem.cost data.exactFill ∧
      smartAllocationSlackReductionOperationCount data.problem ≤
        SmartAllocationProblem.linearRuntimeBound data.problem := by
  simpa [exactFill] using
    Algorithm3ProblemFirstUseSlackCertificate.exactFill_optimal_and_linear_runtime
      data.problemFirstUseSlackCertificate

end Algorithm3SupportCountLoopData

/--
Concrete support-count semantics for the exact output of Algorithm 3.

Unlike `Algorithm3SupportCountLoopData`, this record does not require a source
proof that the loop can realize every hypothetical slack allocation.  It only
records that the output produced by the paper's one-pass loop exactly realizes
the required first-use slack counts.  That is the only realization fact needed
for the fixed-problem optimality theorem.
-/
structure Algorithm3ExactFillSupportCountData
    (Voter Candidate Slack : Type*) [DecidableEq Candidate]
    [Fintype Slack] where
  voters : Finset Voter
  relevantActiveSets : Finset (Finset Candidate)
  requiredSlack : Slack → ℕ
  firstUseCounts :
    ((active : Finset Candidate) → active ∈ relevantActiveSets →
      Candidate → ℕ) → Slack → ℕ
  exactFill : Voter → RCVBallot Candidate
  exactFill_firstUseCounts_eq :
    ∀ slack,
      firstUseCounts
          (relevantActiveSupportCounts voters relevantActiveSets exactFill)
          slack =
        requiredSlack slack
  budget : ℕ
  uniqueBallotCount : ℕ
  candidateCount : ℕ

/--
Executable input data for Algorithm 3's exact-fill support-count semantics.

The proof-carrying `Algorithm3ExactFillSupportCountData` records that the
actual Algorithm 3 output realizes the required first-use slack vector.  This
input record carries only the computable data; the realization fact is supplied
by the finite Boolean checker below.
-/
structure Algorithm3ExactFillSupportCountInputs
    (Voter Candidate Slack : Type*) [DecidableEq Candidate]
    [Fintype Slack] where
  voters : Finset Voter
  relevantActiveSets : Finset (Finset Candidate)
  requiredSlack : Slack → ℕ
  firstUseCounts :
    ((active : Finset Candidate) → active ∈ relevantActiveSets →
      Candidate → ℕ) → Slack → ℕ
  exactFill : Voter → RCVBallot Candidate
  budget : ℕ
  uniqueBallotCount : ℕ
  candidateCount : ℕ

namespace Algorithm3ExactFillSupportCountInputs

/--
Finite Boolean check that Algorithm 3's actual exact-fill output realizes every
required first-use slack component.
-/
noncomputable def exactFillFirstUseCheck
    {Voter Candidate Slack : Type*} [DecidableEq Candidate]
    [Fintype Slack] [DecidableEq Slack]
    (inputs : Algorithm3ExactFillSupportCountInputs Voter Candidate Slack) :
    Bool :=
  (Finset.univ : Finset Slack).toList.all fun slack =>
    decide
      (inputs.firstUseCounts
          (relevantActiveSupportCounts inputs.voters
            inputs.relevantActiveSets inputs.exactFill) slack =
        inputs.requiredSlack slack)

/--
A successful exact-fill first-use checker gives the realization equality needed
by the proof-carrying Algorithm 3 support-count data.
-/
theorem exactFill_firstUseCounts_eq_of_check_eq_true
    {Voter Candidate Slack : Type*} [DecidableEq Candidate]
    [Fintype Slack] [DecidableEq Slack]
    (inputs : Algorithm3ExactFillSupportCountInputs Voter Candidate Slack)
    (hcheck : inputs.exactFillFirstUseCheck = true) :
    ∀ slack,
      inputs.firstUseCounts
          (relevantActiveSupportCounts inputs.voters
            inputs.relevantActiveSets inputs.exactFill) slack =
        inputs.requiredSlack slack := by
  intro slack
  have hall :
      ∀ slack ∈ (Finset.univ : Finset Slack).toList,
        decide
            (inputs.firstUseCounts
                (relevantActiveSupportCounts inputs.voters
                  inputs.relevantActiveSets inputs.exactFill) slack =
              inputs.requiredSlack slack) = true := by
    exact List.all_eq_true.mp (by
      simpa [exactFillFirstUseCheck] using hcheck)
  exact decide_eq_true_iff.mp (hall slack (by simp))

/--
Componentwise realization of every first-use slack component is exactly what
the finite exact-fill checker verifies.
-/
theorem exactFillFirstUseCheck_eq_true_of_forall
    {Voter Candidate Slack : Type*} [DecidableEq Candidate]
    [Fintype Slack] [DecidableEq Slack]
    (inputs : Algorithm3ExactFillSupportCountInputs Voter Candidate Slack)
    (h :
      ∀ slack,
        inputs.firstUseCounts
            (relevantActiveSupportCounts inputs.voters
              inputs.relevantActiveSets inputs.exactFill) slack =
          inputs.requiredSlack slack) :
    inputs.exactFillFirstUseCheck = true := by
  exact List.all_eq_true.mpr (by
    intro slack _hmem
    exact decide_eq_true_iff.mpr (h slack))

/--
Convert executable Algorithm 3 exact-fill inputs and a successful finite check
into the proof-carrying data consumed by the Theorem 3.1 optimization proof.
-/
def toData
    {Voter Candidate Slack : Type*} [DecidableEq Candidate]
    [Fintype Slack] [DecidableEq Slack]
    (inputs : Algorithm3ExactFillSupportCountInputs Voter Candidate Slack)
    (hcheck : inputs.exactFillFirstUseCheck = true) :
    Algorithm3ExactFillSupportCountData Voter Candidate Slack where
  voters := inputs.voters
  relevantActiveSets := inputs.relevantActiveSets
  requiredSlack := inputs.requiredSlack
  firstUseCounts := inputs.firstUseCounts
  exactFill := inputs.exactFill
  exactFill_firstUseCounts_eq :=
    inputs.exactFill_firstUseCounts_eq_of_check_eq_true hcheck
  budget := inputs.budget
  uniqueBallotCount := inputs.uniqueBallotCount
  candidateCount := inputs.candidateCount

end Algorithm3ExactFillSupportCountInputs

/--
Executable active-support input data for Algorithm 3 exact filling.

This specializes `Algorithm3ExactFillSupportCountInputs` to the source case
where each slack component is a concrete round-local active set and candidate,
and its first-use count is the active-support count of the exact-fill ballot
addition at that component.
-/
structure Algorithm3ActiveSupportExactFillInputs
    (Voter Candidate Slack : Type*) [DecidableEq Candidate]
    [Fintype Slack] where
  voters : Finset Voter
  relevantActiveSets : Finset (Finset Candidate)
  requiredSlack : Slack → ℕ
  activeOf : Slack → Finset Candidate
  active_mem : ∀ slack, activeOf slack ∈ relevantActiveSets
  candidateOf : Slack → Candidate
  exactFill : Voter → RCVBallot Candidate
  budget : ℕ
  uniqueBallotCount : ℕ
  candidateCount : ℕ

namespace Algorithm3ActiveSupportExactFillInputs

/-- First-use counts induced by active-support counts at each slack component. -/
def firstUseCounts
    {Voter Candidate Slack : Type*} [DecidableEq Candidate]
    [Fintype Slack]
    (inputs :
      Algorithm3ActiveSupportExactFillInputs Voter Candidate Slack)
    (counts :
      (active : Finset Candidate) → active ∈ inputs.relevantActiveSets →
        Candidate → ℕ) (slack : Slack) : ℕ :=
  counts (inputs.activeOf slack) (inputs.active_mem slack)
    (inputs.candidateOf slack)

/--
Forget active-support component structure, keeping the generic support-count
exact-fill input record.
-/
def toExactFillSupportCountInputs
    {Voter Candidate Slack : Type*} [DecidableEq Candidate]
    [Fintype Slack]
    (inputs :
      Algorithm3ActiveSupportExactFillInputs Voter Candidate Slack) :
    Algorithm3ExactFillSupportCountInputs Voter Candidate Slack where
  voters := inputs.voters
  relevantActiveSets := inputs.relevantActiveSets
  requiredSlack := inputs.requiredSlack
  firstUseCounts := inputs.firstUseCounts
  exactFill := inputs.exactFill
  budget := inputs.budget
  uniqueBallotCount := inputs.uniqueBallotCount
  candidateCount := inputs.candidateCount

/--
Finite Boolean check that the exact-fill ballots realize every component's
required active-support slack.
-/
noncomputable def exactFillActiveSupportCheck
    {Voter Candidate Slack : Type*} [DecidableEq Candidate]
    [Fintype Slack] [DecidableEq Slack]
    (inputs :
      Algorithm3ActiveSupportExactFillInputs Voter Candidate Slack) :
    Bool :=
  (Finset.univ : Finset Slack).toList.all fun slack =>
    decide
      ((Ballot.activeSupport inputs.voters inputs.exactFill
          (inputs.activeOf slack) (inputs.candidateOf slack)).card =
        inputs.requiredSlack slack)

/--
Componentwise active-support realization is exactly what the finite
active-support exact-fill checker verifies.
-/
theorem exactFillActiveSupportCheck_eq_true_of_forall
    {Voter Candidate Slack : Type*} [DecidableEq Candidate]
    [Fintype Slack] [DecidableEq Slack]
    (inputs :
      Algorithm3ActiveSupportExactFillInputs Voter Candidate Slack)
    (h :
      ∀ slack,
        (Ballot.activeSupport inputs.voters inputs.exactFill
          (inputs.activeOf slack) (inputs.candidateOf slack)).card =
          inputs.requiredSlack slack) :
    inputs.exactFillActiveSupportCheck = true := by
  exact List.all_eq_true.mpr (by
    intro slack _hmem
    exact decide_eq_true_iff.mpr (h slack))

/--
Finite Boolean check for Algorithm 3 voter-block witnesses.  For every
round-local slack component, the proposed block must be a subset of the source
voters, have the required cardinality, and exactly match the voters whose
exact-fill ballot first supports the component's candidate at that component's
active set.
-/
noncomputable def exactFillActiveSupportVoterBlockCheck
    {Voter Candidate Slack : Type*} [DecidableEq Voter]
    [DecidableEq Candidate] [Fintype Slack] [DecidableEq Slack]
    (inputs :
      Algorithm3ActiveSupportExactFillInputs Voter Candidate Slack)
    (blocks : Slack → Finset Voter) : Bool :=
  (Finset.univ : Finset Slack).toList.all fun slack =>
    decide (blocks slack ⊆ inputs.voters) &&
      (decide ((blocks slack).card = inputs.requiredSlack slack) &&
        inputs.voters.toList.all fun voter =>
          decide
            (Ballot.nextActive (inputs.exactFill voter)
                  (inputs.activeOf slack) =
                some (inputs.candidateOf slack) ↔
              voter ∈ blocks slack))

/--
A successful voter-block checker supplies the subset, cardinality, and
next-active iff facts used by the active-support realization proof.
-/
theorem exactFillActiveSupportVoterBlockCheck_facts
    {Voter Candidate Slack : Type*} [DecidableEq Voter]
    [DecidableEq Candidate] [Fintype Slack] [DecidableEq Slack]
    (inputs :
      Algorithm3ActiveSupportExactFillInputs Voter Candidate Slack)
    (blocks : Slack → Finset Voter)
    (hcheck : inputs.exactFillActiveSupportVoterBlockCheck blocks = true) :
    (∀ slack, blocks slack ⊆ inputs.voters) ∧
      (∀ slack, (blocks slack).card = inputs.requiredSlack slack) ∧
      (∀ slack voter, voter ∈ inputs.voters →
        (Ballot.nextActive (inputs.exactFill voter) (inputs.activeOf slack) =
              some (inputs.candidateOf slack) ↔
            voter ∈ blocks slack)) := by
  have hslack_all :
      ∀ slack ∈ (Finset.univ : Finset Slack).toList,
        (decide (blocks slack ⊆ inputs.voters) &&
            (decide ((blocks slack).card = inputs.requiredSlack slack) &&
              inputs.voters.toList.all fun voter =>
                decide
                  (Ballot.nextActive (inputs.exactFill voter)
                        (inputs.activeOf slack) =
                      some (inputs.candidateOf slack) ↔
                    voter ∈ blocks slack))) = true := by
    exact List.all_eq_true.mp (by
      simpa [exactFillActiveSupportVoterBlockCheck] using hcheck)
  refine ⟨?_, ?_, ?_⟩
  · intro slack
    have hparts :
        decide (blocks slack ⊆ inputs.voters) = true ∧
          decide ((blocks slack).card = inputs.requiredSlack slack) = true ∧
          (inputs.voters.toList.all fun voter =>
            decide
              (Ballot.nextActive (inputs.exactFill voter)
                    (inputs.activeOf slack) =
                  some (inputs.candidateOf slack) ↔
                voter ∈ blocks slack)) = true := by
      simpa [Bool.and_eq_true_eq_eq_true_and_eq_true] using
        hslack_all slack (by simp)
    exact of_decide_eq_true hparts.1
  · intro slack
    have hparts :
        decide (blocks slack ⊆ inputs.voters) = true ∧
          decide ((blocks slack).card = inputs.requiredSlack slack) = true ∧
          (inputs.voters.toList.all fun voter =>
            decide
              (Ballot.nextActive (inputs.exactFill voter)
                    (inputs.activeOf slack) =
                  some (inputs.candidateOf slack) ↔
                voter ∈ blocks slack)) = true := by
      simpa [Bool.and_eq_true_eq_eq_true_and_eq_true] using
        hslack_all slack (by simp)
    exact of_decide_eq_true hparts.2.1
  · intro slack voter hvoter
    have hparts :
        decide (blocks slack ⊆ inputs.voters) = true ∧
          decide ((blocks slack).card = inputs.requiredSlack slack) = true ∧
          (inputs.voters.toList.all fun voter =>
            decide
              (Ballot.nextActive (inputs.exactFill voter)
                    (inputs.activeOf slack) =
                  some (inputs.candidateOf slack) ↔
                voter ∈ blocks slack)) = true := by
      simpa [Bool.and_eq_true_eq_eq_true_and_eq_true] using
        hslack_all slack (by simp)
    exact
      of_decide_eq_true
        ((List.all_eq_true.mp hparts.2.2) voter
          (Finset.mem_toList.mpr hvoter))

/--
The voter-block checker is complete for the displayed subset, cardinality, and
next-active iff obligations.
-/
theorem exactFillActiveSupportVoterBlockCheck_eq_true_of_facts
    {Voter Candidate Slack : Type*} [DecidableEq Voter]
    [DecidableEq Candidate] [Fintype Slack] [DecidableEq Slack]
    (inputs :
      Algorithm3ActiveSupportExactFillInputs Voter Candidate Slack)
    (blocks : Slack → Finset Voter)
    (hblocks_subset : ∀ slack, blocks slack ⊆ inputs.voters)
    (hblocks_card : ∀ slack, (blocks slack).card = inputs.requiredSlack slack)
    (hnext_iff :
      ∀ slack voter, voter ∈ inputs.voters →
        (Ballot.nextActive (inputs.exactFill voter) (inputs.activeOf slack) =
              some (inputs.candidateOf slack) ↔
            voter ∈ blocks slack)) :
    inputs.exactFillActiveSupportVoterBlockCheck blocks = true := by
  exact List.all_eq_true.mpr (by
    intro slack _hslack
    rw [Bool.and_eq_true_eq_eq_true_and_eq_true]
    refine ⟨decide_eq_true_iff.mpr (hblocks_subset slack), ?_⟩
    rw [Bool.and_eq_true_eq_eq_true_and_eq_true]
    refine ⟨decide_eq_true_iff.mpr (hblocks_card slack), ?_⟩
    exact List.all_eq_true.mpr (by
      intro voter hvoter
      exact decide_eq_true_iff.mpr
        (hnext_iff slack voter (Finset.mem_toList.mp hvoter))))

/--
Per-component voter blocks prove Algorithm 3 exact-fill realization.

The source allocation proof can discharge the active-support equality by
exhibiting, for each round-local slack component, the exact block of added
voters that first supports the component's candidate at that component's active
set.  The block cardinality supplies the required slack, and the next-active
iff proves that no other added voter contributes to that component.
-/
theorem exactFill_activeSupport_eq_requiredSlack_of_voterBlocks
    {Voter Candidate Slack : Type*} [DecidableEq Candidate]
    [Fintype Slack]
    (inputs :
      Algorithm3ActiveSupportExactFillInputs Voter Candidate Slack)
    (blocks : Slack → Finset Voter)
    (hblocks_subset : ∀ slack, blocks slack ⊆ inputs.voters)
    (hblocks_card : ∀ slack, (blocks slack).card = inputs.requiredSlack slack)
    (hnext_iff :
      ∀ slack voter, voter ∈ inputs.voters →
        (Ballot.nextActive (inputs.exactFill voter) (inputs.activeOf slack) =
              some (inputs.candidateOf slack) ↔
            voter ∈ blocks slack)) :
    ∀ slack,
      (Ballot.activeSupport inputs.voters inputs.exactFill
        (inputs.activeOf slack) (inputs.candidateOf slack)).card =
        inputs.requiredSlack slack := by
  intro slack
  have hsupport_eq :
      Ballot.activeSupport inputs.voters inputs.exactFill
          (inputs.activeOf slack) (inputs.candidateOf slack) =
        blocks slack := by
    ext voter
    by_cases hvoter : voter ∈ inputs.voters
    · simp [Ballot.activeSupport, hvoter, hnext_iff slack voter hvoter]
    · have hnot_block : voter ∉ blocks slack := by
        intro hblock
        exact hvoter ((hblocks_subset slack) hblock)
      simp [Ballot.activeSupport, hvoter, hnot_block]
  rw [hsupport_eq, hblocks_card]

/--
A successful finite voter-block checker proves Algorithm 3 exact-fill
realization for every active-support component.
-/
theorem exactFill_activeSupport_eq_requiredSlack_of_voterBlockCheck
    {Voter Candidate Slack : Type*} [DecidableEq Voter]
    [DecidableEq Candidate] [Fintype Slack] [DecidableEq Slack]
    (inputs :
      Algorithm3ActiveSupportExactFillInputs Voter Candidate Slack)
    (blocks : Slack → Finset Voter)
    (hcheck : inputs.exactFillActiveSupportVoterBlockCheck blocks = true) :
    ∀ slack,
      (Ballot.activeSupport inputs.voters inputs.exactFill
        (inputs.activeOf slack) (inputs.candidateOf slack)).card =
        inputs.requiredSlack slack := by
  have hfacts :=
    inputs.exactFillActiveSupportVoterBlockCheck_facts blocks hcheck
  exact
    inputs.exactFill_activeSupport_eq_requiredSlack_of_voterBlocks
      blocks hfacts.1 hfacts.2.1 hfacts.2.2

/--
The active-support exact-fill checker is the generic first-use checker after
forgetting the active-support component structure.
-/
theorem exactFillFirstUseCheck_eq_exactFillActiveSupportCheck
    {Voter Candidate Slack : Type*} [DecidableEq Candidate]
    [Fintype Slack] [DecidableEq Slack]
    (inputs :
      Algorithm3ActiveSupportExactFillInputs Voter Candidate Slack) :
    inputs.toExactFillSupportCountInputs.exactFillFirstUseCheck =
      inputs.exactFillActiveSupportCheck := by
  rfl

/--
A successful active-support exact-fill checker supplies the generic
support-count exact-fill checker used by the Theorem 3.1 proof.
-/
theorem exactFillFirstUseCheck_eq_true_of_activeSupportCheck_eq_true
    {Voter Candidate Slack : Type*} [DecidableEq Candidate]
    [Fintype Slack] [DecidableEq Slack]
    (inputs :
      Algorithm3ActiveSupportExactFillInputs Voter Candidate Slack)
    (hcheck : inputs.exactFillActiveSupportCheck = true) :
    inputs.toExactFillSupportCountInputs.exactFillFirstUseCheck = true := by
  rwa [inputs.exactFillFirstUseCheck_eq_exactFillActiveSupportCheck]

end Algorithm3ActiveSupportExactFillInputs

namespace Algorithm3SupportCountLoopData

/--
The computable exact-fill input record obtained from the stronger Algorithm 3
support-count loop semantics.
-/
def exactFillSupportCountInputs
    {Voter Candidate Slack : Type*} [DecidableEq Candidate] [Fintype Slack]
    (data : Algorithm3SupportCountLoopData Voter Candidate Slack) :
    Algorithm3ExactFillSupportCountInputs Voter Candidate Slack where
  voters := data.voters
  relevantActiveSets := data.relevantActiveSets
  requiredSlack := data.requiredSlack
  firstUseCounts := data.firstUseCounts
  exactFill := data.exactFill
  budget := data.budget
  uniqueBallotCount := data.uniqueBallotCount
  candidateCount := data.candidateCount

/--
The stronger Algorithm 3 support-count loop semantics imply that the finite
exact-fill checker succeeds for the extracted exact-fill input record.
-/
theorem exactFillSupportCountInputs_exactFillFirstUseCheck
    {Voter Candidate Slack : Type*} [DecidableEq Candidate]
    [Fintype Slack] [DecidableEq Slack]
    (data : Algorithm3SupportCountLoopData Voter Candidate Slack) :
    data.exactFillSupportCountInputs.exactFillFirstUseCheck = true := by
  refine
    Algorithm3ExactFillSupportCountInputs.exactFillFirstUseCheck_eq_true_of_forall
      data.exactFillSupportCountInputs ?_
  intro slack
  simpa [exactFillSupportCountInputs, exactFill] using
    data.exactFill_firstUseCounts_eq data.requiredSlack slack

end Algorithm3SupportCountLoopData

namespace Algorithm3ExactFillSupportCountData

/-- Feasibility generated by Algorithm 3 first-use support counts. -/
def feasibleCounts {Voter Candidate Slack : Type*} [DecidableEq Candidate]
    [Fintype Slack]
    (data : Algorithm3ExactFillSupportCountData Voter Candidate Slack)
    (counts :
      (active : Finset Candidate) → active ∈ data.relevantActiveSets →
        Candidate → ℕ) : Prop :=
  ∀ slack, data.requiredSlack slack ≤ data.firstUseCounts counts slack

/-- Objective generated by Algorithm 3 first-use support counts. -/
def costCounts {Voter Candidate Slack : Type*} [DecidableEq Candidate]
    [Fintype Slack]
    (data : Algorithm3ExactFillSupportCountData Voter Candidate Slack)
    (counts :
      (active : Finset Candidate) → active ∈ data.relevantActiveSets →
        Candidate → ℕ) : ℝ :=
  ∑ slack, (data.firstUseCounts counts slack : ℝ)

/--
The support-count SmartAllocation data induced by concrete exact-fill
Algorithm 3 semantics.
-/
def supportCountData {Voter Candidate Slack : Type*} [DecidableEq Candidate]
    [Fintype Slack]
    (data : Algorithm3ExactFillSupportCountData Voter Candidate Slack) :
    SupportCountSmartAllocationData Voter Candidate where
  voters := data.voters
  relevantActiveSets := data.relevantActiveSets
  feasibleCounts := data.feasibleCounts
  costCounts := data.costCounts
  budget := data.budget
  uniqueBallotCount := data.uniqueBallotCount
  candidateCount := data.candidateCount

/-- The SmartAllocation problem generated by exact-fill first-use semantics. -/
def problem {Voter Candidate Slack : Type*} [DecidableEq Candidate]
    [Fintype Slack]
    (data : Algorithm3ExactFillSupportCountData Voter Candidate Slack) :
    SmartAllocationProblem (Voter → RCVBallot Candidate) :=
  data.supportCountData.problem

/-- First-use counts assigned to a concrete strategic addition. -/
def firstUse {Voter Candidate Slack : Type*} [DecidableEq Candidate]
    [Fintype Slack]
    (data : Algorithm3ExactFillSupportCountData Voter Candidate Slack)
    (addition : Voter → RCVBallot Candidate) : Slack → ℕ :=
  data.firstUseCounts
    (relevantActiveSupportCounts data.voters data.relevantActiveSets addition)

/--
Exact-fill Algorithm 3 semantics instantiate the fixed-problem first-use
certificate used by the checked componentwise slack theorem.
-/
def problemFirstUseSlackCertificate
    {Voter Candidate Slack : Type*} [DecidableEq Candidate] [Fintype Slack]
    (data : Algorithm3ExactFillSupportCountData Voter Candidate Slack) :
    Algorithm3ProblemFirstUseSlackCertificate
      (Voter → RCVBallot Candidate) Slack data.problem where
  requiredSlack := data.requiredSlack
  firstUse := data.firstUse
  exactFillAddition := fun _allocation => data.exactFill
  exact_fill_feasible := by
    intro _allocation _hallocation slack
    change
      data.requiredSlack slack ≤
        data.firstUseCounts
          (relevantActiveSupportCounts data.voters data.relevantActiveSets
            data.exactFill) slack
    rw [data.exactFill_firstUseCounts_eq slack]
  feasible_addition_fills_required_first_use := by
    intro addition hfeasible slack
    simpa [problem, supportCountData, SupportCountSmartAllocationData.problem,
      feasibleCounts, firstUse] using
      (hfeasible slack)
  exact_fill_cost_eq_required_slack_sum := by
    simp [problem, supportCountData, SupportCountSmartAllocationData.problem,
      costCounts, data.exactFill_firstUseCounts_eq]
  feasible_addition_cost_eq_first_use_sum := by
    intro addition _hfeasible
    rfl

/--
Algorithm 3's exact-fill support-count semantics prove optimality and the exact
`m * n` operation bound for the generated SmartAllocation problem.
-/
theorem exactFill_optimal_and_linear_runtime
    {Voter Candidate Slack : Type*} [DecidableEq Candidate] [Fintype Slack]
    (data : Algorithm3ExactFillSupportCountData Voter Candidate Slack) :
    EconCSLib.Optimization.IsMinimizerOn
        data.problem.feasible data.problem.cost data.exactFill ∧
      smartAllocationSlackReductionOperationCount data.problem ≤
        SmartAllocationProblem.linearRuntimeBound data.problem := by
  simpa using
    Algorithm3ProblemFirstUseSlackCertificate.exactFill_optimal_and_linear_runtime
      data.problemFirstUseSlackCertificate

end Algorithm3ExactFillSupportCountData

namespace Algorithm3ExactFillSupportCountInputs

/--
Checked Algorithm 3 exact-fill support-count inputs prove optimality and the
exact `m * n` operation bound for the generated SmartAllocation problem.
-/
theorem exactFill_optimal_and_linear_runtime_of_check
    {Voter Candidate Slack : Type*} [DecidableEq Candidate]
    [Fintype Slack] [DecidableEq Slack]
    (inputs : Algorithm3ExactFillSupportCountInputs Voter Candidate Slack)
    (hcheck : inputs.exactFillFirstUseCheck = true) :
    EconCSLib.Optimization.IsMinimizerOn
        (inputs.toData hcheck).problem.feasible
        (inputs.toData hcheck).problem.cost
        inputs.exactFill ∧
      smartAllocationSlackReductionOperationCount
          (inputs.toData hcheck).problem ≤
        SmartAllocationProblem.linearRuntimeBound
          (inputs.toData hcheck).problem := by
  simpa [toData] using
    Algorithm3ExactFillSupportCountData.exactFill_optimal_and_linear_runtime
      (inputs.toData hcheck)

end Algorithm3ExactFillSupportCountInputs

namespace Algorithm3ActiveSupportExactFillInputs

/--
Checked active-support Algorithm 3 exact-fill inputs prove optimality and the
exact `m * n` operation bound for the generated SmartAllocation problem.
-/
theorem exactFill_optimal_and_linear_runtime_of_activeSupportCheck
    {Voter Candidate Slack : Type*} [DecidableEq Candidate]
    [Fintype Slack] [DecidableEq Slack]
    (inputs :
      Algorithm3ActiveSupportExactFillInputs Voter Candidate Slack)
    (hcheck : inputs.exactFillActiveSupportCheck = true) :
    EconCSLib.Optimization.IsMinimizerOn
        ((inputs.toExactFillSupportCountInputs.toData
          (inputs.exactFillFirstUseCheck_eq_true_of_activeSupportCheck_eq_true
            hcheck)).problem.feasible)
        ((inputs.toExactFillSupportCountInputs.toData
          (inputs.exactFillFirstUseCheck_eq_true_of_activeSupportCheck_eq_true
            hcheck)).problem.cost)
        inputs.exactFill ∧
      smartAllocationSlackReductionOperationCount
          ((inputs.toExactFillSupportCountInputs.toData
            (inputs.exactFillFirstUseCheck_eq_true_of_activeSupportCheck_eq_true
              hcheck)).problem) ≤
        SmartAllocationProblem.linearRuntimeBound
          ((inputs.toExactFillSupportCountInputs.toData
            (inputs.exactFillFirstUseCheck_eq_true_of_activeSupportCheck_eq_true
              hcheck)).problem) := by
  exact
    Algorithm3ExactFillSupportCountInputs.exactFill_optimal_and_linear_runtime_of_check
      inputs.toExactFillSupportCountInputs
      (inputs.exactFillFirstUseCheck_eq_true_of_activeSupportCheck_eq_true
        hcheck)

end Algorithm3ActiveSupportExactFillInputs

/--
Theorem 3.1 source-model route: if Algorithm 3's concrete STV dynamics
instantiate the first-use slack model, then SmartAllocation is optimal and
satisfies the source linear operation bound.
-/
theorem theorem3_1_smartAllocation_optimal_and_linear_runtime_of_firstUseSlackModel
    {Addition Slack : Type*} [Fintype Slack]
    (model : SmartAllocationFirstUseSlackModel Addition Slack)
    (problem : SmartAllocationProblem Addition) :
    EconCSLib.Optimization.IsMinimizerOn
        problem.feasible problem.cost
        (smartAllocationSlackReductionAlgorithm model.slackProblem
          model.additionOf problem) ∧
      smartAllocationSlackReductionOperationCount problem ≤
        SmartAllocationProblem.linearRuntimeBound problem :=
  model.concreteSlackReduction_optimal_and_linear_runtime problem

end DGJ24OptimalStrategiesRCV
