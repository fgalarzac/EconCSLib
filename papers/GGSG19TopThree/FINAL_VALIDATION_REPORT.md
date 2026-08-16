# Final Validation Report: Who is in Your Top Three?
Updated: 2026-08-16

## 1. Human Verdict

Formalized. The ranking model, all named theoretical results, and the Mallows
joint-location algorithm are covered. Proposition 1 includes the exact-tie
case under the paper's independent uniform tie breaking, and the dynamic
program gives exact arbitrary-pair Mallows locations. No substantial
source-paper error was found. Independent human review has not yet been
recorded.

## 2. Closeout Status

- Completion status: formalized.
- Normal scope: the ranking definitions, Propositions 1--4, Theorems 1--2,
  the Mallows corollary, the mathematical examples, and the joint-location
  algorithm.
- Independent human review has not yet been recorded.

## 3. Source and Scope

The source is [Who Is in Your Top Three?](https://arxiv.org/pdf/1906.08160),
HCOMP 2019. The reviewed scope is its finite ranking model, three definitions,
nine named results, displayed rate formulas, mathematical examples, and the
Mallows joint-location algorithm. Empirical estimates, figure rendering, and
deployment recommendations are outside this mathematical scope.

## 4. Researcher Summary of Checked Results

- The three definitions specify the limiting outcome, its exponential rate,
  and the feasible rule that maximizes that rate.
- Proposition 1 characterizes design invariance using cross-tier prefix
  separation, including the paper's exact-tie case with uniform tie breaking.
- Propositions 2--4 establish the pairwise and aggregate error rates, including
  the finite-sample exponential bound.
- Theorems 1--2 cover arbitrary finite goals and show that randomizing
  K-approval cutoffs cannot improve a fixed pair's rate.
- The Mallows result includes both the deterministic endpoint and the positive
  parameter range. The examples show both a randomized-rule improvement and a
  setting in which W-approval is not rate-optimal.
- The joint-location algorithm gives the exact distribution of two candidates'
  positions under the repeated-insertion Mallows construction, with a
  degree-six arithmetic-operation bound.

## 5. Remaining Boundaries and Gaps

None. The algorithmic result is an arithmetic-operation bound; it does not
make a separate bit-complexity claim.

## 6. Additional Assumptions Beyond Paper

None. The arguments use the paper's finite score-gap law, randomized-rule
weights, nonempty winner tier, proper approval cutoffs, and stated Mallows
parameter ranges. Strict prefix inequalities are part of the characterization,
not an additional premise.

## 7. Proof-Strategy Deviations

For the joint-location result, the source's repeated-insertion description is
expressed as an equivalent finite dynamic program and proved by induction over
the insertion prefixes. The deterministic Mallows endpoint and the positive
parameter case are treated separately, matching their distinct probability
laws.

## 8. Proof Tricks Worth Reusing

- Compare a finite recurrence with its independently defined generative
  process.
- Track each distinguished candidate's location through the insertion stages.
- Count stages, states, and insertion choices separately to obtain the
  polynomial operation bound.
- For a centered finite score-gap walk, combine recurrence with the explicit
  tie-breaking rule to handle both fluctuating and identically tied cases.

## 9. Generalizations, Conjectures, and Extensions

The joint-location method could be extended to sparse reachable-state tables or
to more tracked candidates. Those would be new algorithmic results rather than
claims of this paper.

## 10. Source Clarifications and Exact Readings

None.

## 11. Paper Issues or Caveats

None.
