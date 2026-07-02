# Start Here: DGJ26

Current status: partial formalization, 65 paper-facing rows.

Begin by running:

```bash
lake build EconCSLib.SocialChoice.Voting.STV
lake env lean papers/DGJ26PracticalDynamicsRCV/PaperInterface.lean
```

Read in this order:

0. `../../docs/plans/DGJ_RCV_HANDOFF_2026-07-01.md`
1. `FINAL_VALIDATION_REPORT.md`
2. `FORMALIZATION_PLAN.md`
3. `PaperInterface.lean`
4. `MainTheorems.lean`

DGJ26 is downstream of DGJ24. Prefer waiting for or reusing DGJ24's
SmartAllocation and irrelevant-candidate-removal constructors instead of
duplicating those semantics locally.

Shared-library note: DGJ24 now has an RCVTrace route for Algorithm 7 built on
`STVTrace.roundOutcomeSequence`, `STVTrace.HasInitialEliminationPrefix`, and
`STVTrace.HasInitialEliminationFocusPrefix`. Reuse that trace-to-sequence bridge
for DGJ26 full-election-run extraction instead of creating a paper-local
win/loss replay predicate.

Useful local seams:

- Additional Algorithm A robust-output constructors for Proposition 1 beyond
  the closed append-suffix-then-prefix/support-count-loop routes.
- Proposition 2's exhausted-ballot count-test closeout is now paper-facing:
  `paper_proposition2_multi_round_closeout_from_algorithmA_count_test`.
- Theorem 2.1 now has finite branch checkers for the canonical generated route
  and the full-run post-worst tally route, plus direct concrete
  implementation/runtime endpoints from either those checks or a full Algorithm
  3 run object. Only lower-level extraction of the original replay object from
  a literal executable Algorithm 3 simulator remains if that layer is in scope.
- Theorem 2.2 now has an executable Algorithm 4 no-failed-pair checker,
  direct quadratic implementation endpoint, and a source-shaped checker whose
  Eq. (2)/(3) quantities are extracted from the ballot profile. Remaining work,
  if this layer is in scope, is connecting that source-shaped checker to a full
  multi-winner executable election run rather than supplying the successful
  Boolean check as the endpoint premise.

Do not redo the shared ballot robustness, exhausted-prefix equivalence,
strict-support condition, Proposition 2 count-test closeout, exact Algorithm 4
output theorem, Algorithm 4 run endpoint, Algorithm A
append-suffix-then-prefix/support-count-loop routes, Theorem 2.1 checked branch
routes, Theorem 2.1 full-run initial-loss-prefix bridge, Theorem 2.1 full-run
object endpoint, failure-triggered post-worst constructor, or raw
one-survival step-facts route.
