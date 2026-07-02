# Handoff: 2026-06-29 DGJ26

Historical handoff. For the current continuation plan, use
`../../docs/plans/DGJ_RCV_HANDOFF_2026-07-01.md`.

Stopped at a clean partial-proof boundary.

What is done:

- Ballot-level suffix/prefix robustness and profile active-support robustness
  build.
- Proposition 2 exhausted-ballot completion, viable-set support formulas, and
  the direct Algorithm A count-test closeout build.
- Theorem 2.1 includes the original-branch trace route and the one-survival
  raw step-facts route.
- Theorem 2.2 includes updated strict-support formulas, Eq. (2)/(3) arithmetic,
  the exact Algorithm 4 retained/removed output theorem, and the quadratic
  component-bound implementation route.
- The current curated interface is 65 paper-facing rows in `status.json`.
- README, formalization plan, DAG, and stopping validation report are updated.

What is not done:

- Algorithm A robust-output constructors are still open.
- Full extraction from concrete election runs remains open, including
  Theorem 2.1's source branch and Theorem 2.2's source pairwise inequalities.
- DGJ24 source constructors remain upstream dependencies for the cleanest
  closeout path.

Next proof target:

If DGJ24 constructors are available, reuse them. Otherwise work only on DGJ26
constructors that do not duplicate DGJ24 semantics, especially Algorithm A
robust-output constructors.
For any full-election-run extraction, reuse the shared
`STVTrace.roundOutcomeSequence` / `STVTrace.HasInitialEliminationPrefix` /
`STVTrace.HasInitialEliminationFocusPrefix` bridge and DGJ24's RCVTrace route
rather than introducing a local replay predicate.

Validation target:

```bash
lake build EconCSLib.SocialChoice.Voting.STV
lake env lean papers/DGJ26PracticalDynamicsRCV/PaperInterface.lean
```
