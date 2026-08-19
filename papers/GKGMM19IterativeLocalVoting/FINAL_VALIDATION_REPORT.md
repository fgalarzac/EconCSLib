# Final Validation Report: Iterative Local Voting for Collective Decision-making in Continuous Spaces
Updated: 2026-08-16

## 1. Human Verdict
Partially formalized. Theorems 1--2 and Propositions 1--2 depend on a reusable
stochastic-subgradient convergence theorem. Theorem 3 is established as a
constrained-space alternative and yields the paper's conclusion under the
explicit full-space condition. Independent human review has not yet been
recorded.

## 2. Closeout Status
- Completion status: partially formalized.
- Covered scope: the ILV models, Theorem 3, and the deterministic components of
  Theorems 1--2 and Propositions 1--2.
- Remaining boundary: stochastic-subgradient convergence.
- Human review: independent sign-off has not yet been recorded.

## 3. Source and Scope
The source is Garg, Kamble, Goel, Marn, and Munagala, *Iterative Local Voting
for Collective Decision-making in Continuous Spaces*, JAIR 2019. The normal
scope covers the paper's models and theory; the shared stochastic-subgradient
convergence result remains an external library boundary. The public source is
[the JAIR article](https://www.jair.org/index.php/jair/article/view/11358).

## 4. Researcher Summary of Checked Results
- The ILV definitions and source models are covered.
- Theorems 1--2 and Propositions 1--2 reduce to stochastic-subgradient
  convergence under the paper's stated conditions.
- Theorem 3 gives a constrained-space alternative and the original result in
  full space.

## 5. Remaining Boundaries and Gaps
The remaining boundary for Theorems 1--2 and Propositions 1--2 is a reusable
stochastic-subgradient convergence theorem. In constrained spaces, Theorem 3
gives the stated alternative; full space recovers the paper's conclusion.

## 6. Additional Assumptions Beyond Paper
None.

## 7. Proof-Strategy Deviations
None.

## 8. Proof Tricks Worth Reusing
None.

## 9. Generalizations, Conjectures, and Extensions

The constrained-space version of Theorem 3 is a useful generalization of the
paper's full-space endpoint. A reusable stochastic-subgradient convergence
theorem would close the remaining paper boundary and belongs in the shared
optimization library rather than in a paper-specific assumption.

## 10. Source Clarifications and Exact Readings

For a constrained decision space, a projected limit can have either zero
aggregate direction or no feasible aggregate direction. In the paper's full
space, every aggregate direction is feasible, so the latter alternative is
impossible and the stated conclusion follows. See the [Theorem 3
constrained-space clarification](docs/THEOREM3_CONSTRAINED_SPACE_SOURCE_NOTE.md).

## 11. Paper Issues or Caveats
None. The constrained-space clarification in Section 10 preserves the paper's
full-space Theorem 3 conclusion.
