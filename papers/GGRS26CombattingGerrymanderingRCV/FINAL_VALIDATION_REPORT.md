# Final Validation Report: GGRS26 Combatting Gerrymandering with Ranked Choice Voting
Updated: 2026-08-16

## 1. Human Verdict

Formalized. The normal named-theory scope contains Lemma C.1 and Proposition
1, and both are covered. Independent human review has not yet been recorded.

## 2. Closeout Status

- Completion status: formalized.
- Normal scope: Lemma C.1 and Proposition 1.
- Results: the PAV selector and the two-party STV/PAV rounded seat-share result
  cover all legal ballot-routed transfer choices.
- Human review: independent sign-off has not yet been recorded.

## 3. Source and Scope

The source is *Combatting Gerrymandering with Ranked Choice Voting: an
Experimental Analysis of Multi-member Districts in the United States*,
[Operations Research](https://doi.org/10.1287/opre.2024.1167). The normal
named-theory scope is Lemma C.1 and Proposition 1; the appendix repetition of
the proposition is not a separate result. Empirical data, map generation,
simulations, figures, and runtime discussion are outside this scope.

## 4. Researcher Summary of Checked Results

- Lemma C.1 constructs the leftmost PAV maximizer and identifies it as the
  unique integer in the paper's half-open interval.
- Proposition 1 starts from the stated two-party solid-coalition electorate.
  Every legal terminal STV execution, and the selected PAV outcome, has a
  Republican seat count in `{floor (y_R M), ceil (y_R M)}`. The result includes
  the paper's tie convention and establishes that the execution domain is
  nonempty.

## 5. Remaining Boundaries and Gaps

None for named theory. The unnumbered map-generation and runtime discussion is
outside the mathematical scope.

## 6. Additional Assumptions Beyond Paper

None.

## 7. Proof-Strategy Deviations

None.

## 8. Proof Tricks Worth Reusing

- State transfer semantics on actual ballot weights and establish a nonempty
  execution domain alongside a universal execution result.
- Express a tie-broken optimizer relationally and establish its totality and
  uniqueness.

## 9. Generalizations, Conjectures, and Extensions

The rounded seat-share conclusion holds for every legal tie choice. No further
generalization is claimed.

## 10. Source Clarifications and Exact Readings

The appendix proof temporarily assumes turnout divisibility by `M + 1`, while
the proposition does not. The proposition's stated turnout bound supports the
needed floor-Droop arithmetic. The precise source-proof reading is in
[Source Clarifications](docs/SOURCE_CLARIFICATIONS.md); it does not change the
result.

## 11. Paper Issues or Caveats

None.
