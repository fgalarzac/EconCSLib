# Final Validation Report: User-Item Fairness Tradeoffs in Recommendations
Updated: 2026-08-16

## 1. Human Verdict

**Formalized.** The paper's named definitions, lemmas, propositions, and
theorems, including its Appendix D/E results, have closed proofs. Appendix E
Lemma 15 contains a localized display typo; the corrected formula is proved and
the printed display is not treated as a theorem. Independent human review has
not yet been recorded.

## 2. Closeout Status

- Completion status: `formalized`.
- Scope: the paper's named theoretical results, including Appendix D/E.
- Human review: not yet recorded.

## 3. Source and Scope

The source is [*User-Item Fairness Tradeoffs in Recommendations*
](https://openreview.net/pdf?id=ZOZjMs3JTs). The formalized surface is its
named definitions, lemmas, propositions, and theorems, including Appendix D/E.
Example 1 and the paper's empirical methods are outside this named-theory
surface and are not counted as formalized results.

## 4. Researcher Summary of Checked Results

- D4 constructs the unique Problem 6 optimizer and proves its two-sided
  threshold support from primitive model conditions.
- D5 derives the optimizer value and every displayed `x`/`y` coordinate.
- D6--D7 prove the optimal-policy type-utility order and monotonicity of the
  actual unique optimizer's pivot.
- D10--D11 prove the midpoint pivot bound and optimal item-fairness
  monotonicity on a selected-pivot interval.
- E13 represents the source's basic-feasible qualifier for the actual
  mirror-restricted Problem 11 equality-feasible polytope by its standard
  extreme-point characterization, then derives the full pivot support pattern.
- E14 constructs and proves uniqueness of the global Problem 11 optimum.
- E15 derives every noncenter coordinate and the corrected center branch for
  an arbitrary global optimum.
- E17 proves right-half zero support for every global optimum without a BFS
  or pivot-support premise.

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

In Appendix E Lemma 15, the Problem 11 center item equation must retain both
mirrored known-type contributions. At the center, `q_t = 1/2`, so the full
equation gives

`lambda = 1 / (1 + L_t)`.

The printed expression is false. The checked witness `n = 3`, `beta = 2/5`,
`q_t = 1/2`, and `L_t = 4/3` gives corrected value `3/7` and printed value
`9/25`.

### Appendix E source note

The corrected E15 theorem is proved. Its false printed center display is
retained as a source-typo note because it is confined to an appendix
derivation and does not leave a main-text or downstream theorem obligation
open. A pinned source revision can fix the display, but it is not required for
the paper's `formalized` status.

## 11. Paper Issues or Caveats

None. The Appendix E Lemma 15 display noted above is a localized source typo,
not a limitation on the paper's status.
