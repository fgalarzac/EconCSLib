# Final Validation Report: KR21 Monoculture
Updated: 2026-08-16

## 1. Human Verdict

**Formalized.** The paper's Definitions 1--4, Theorems 1--9, and Lemmas 1--8
have closed proofs on their stated models. Independent human review has not
yet been recorded.

## 2. Closeout Status

- Completion status: `formalized`.
- Scope: Definitions 1--4, Theorems 1--9, and Lemmas 1--8.
- Human review: not yet recorded.

## 3. Source and Scope

The source is [arXiv:2101.05853](https://arxiv.org/abs/2101.05853).
The formalized surface is its named definitions, theorems, and lemmas.
Computational illustrations, numerical and figure observations, and the
source's stated open observation are not claimed as proved theorems.

## 4. Researcher Summary of Checked Results

The results cover the two-firm game, the Gaussian, Laplace, Gumbel, general
RUM, and Mallows models, together with the named Appendix results. The
outer-distribution results retain the paper's conditional-iid ranking
experiment, integrability conditions, and payoff conclusions. Theorem 3 gives
one common witness for all three terminal payoff inequalities.

## 5. Remaining Boundaries and Gaps

None.

## 6. Additional Assumptions Beyond Paper

None.

## 7. Proof-Strategy Deviations

None.

## 8. Proof Tricks Worth Reusing

None.

## 9. Generalizations, Conjectures, and Extensions

No additional generalization is established here.

## 10. Source Clarifications and Exact Readings

| Source item | Exact reading |
|---|---|
| Theorem 3 | The strict Mallows target is formulated for at least three candidates. |
| Theorem 5 | The proved density condition is global absolute continuity with integrable derivative (`W^{1,1}`). |
| Appendix C Lemma 1 | The formulation is weak globally and strict on the stated overlap region; its source anchors and row-level evidence are in the [paper statement map](audit/paper_statement_map.json). |
| Gumbel/Plackett--Luce identification | With innovation scale `s`, the rate is `theta / s`; the source normalization fixes `s = sqrt(6)/pi`. |

## 11. Paper Issues or Caveats

None. The clarifications above preserve the advertised endpoints and are not
status-bearing caveats.
