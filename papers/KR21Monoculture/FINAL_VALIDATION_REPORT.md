# Final Validation Report: KR21 Monoculture
Updated: 2026-08-16

## 1. Human Verdict

**Formalized.** The paper's Definitions 1--4 and Theorems 1--9 have closed
proofs on their stated models. Appendix C Lemma 1's global strict Laplace
formulation is false as written; the correct weak-global and strict-overlap
forms are proved, and suffice for the paper's named results. Independent human
review has not yet been recorded.

## 2. Closeout Status

- Completion status: `formalized`.
- Scope: Definitions 1--4, Theorems 1--9, and Lemmas 1--8, with Appendix C
  Lemma 1 represented by its correct weak-global and strict-overlap forms.
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

Appendix C Lemma 1 states that Laplace noise is globally strictly well ordered.
That strict condition is false: separated ordered pairs yield equality. The
formal proof uses the globally valid weak inequality and proves strictness on
the explicit overlap region. No named main-text result depends on the false
global strict form; those results remain proved on their stated models.

## 8. Proof Tricks Worth Reusing

None.

## 9. Generalizations, Conjectures, and Extensions

No additional generalization is established here.

## 10. Source Clarifications and Exact Readings

| Source item | Exact reading |
|---|---|
| Theorem 3 | The strict Mallows target is formulated for at least three candidates. |
| Theorem 5 | The proved density condition is global absolute continuity with integrable derivative (`W^{1,1}`). |
| Appendix C Lemma 1 | The printed global strict Laplace form is false. The correct reading is weak globally and strict on the stated overlap region; see the [Appendix C Lemma 1 source clarification](docs/LAPLACIAN_SOURCE_CLARIFICATION.md). The [paper statement map](audit/paper_statement_map.json) records the source anchors and row-level evidence. |
| Gumbel/Plackett--Luce identification | With innovation scale `s`, the rate is `theta / s`; the source normalization fixes `s = sqrt(6)/pi`. |

## 11. Paper Issues or Caveats

None for the named main-text results. The Appendix C Lemma 1 correction is a
source-proof deviation, not a status-bearing caveat for those results.
