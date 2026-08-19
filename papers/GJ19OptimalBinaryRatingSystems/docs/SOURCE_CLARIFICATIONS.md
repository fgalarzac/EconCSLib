# Source Clarifications: GJ19 Optimal Binary Rating Systems

This note records the local source issues referenced in the final validation
report.  Each entry gives a byte-pinned cited-publication anchor, the checked
reading, and its effect on the paper-level conclusion.  These are
clarifications or local corrections; none changes an advertised result.

| Source anchor | Clarification or correction | Effect |
| --- | --- | --- |
| Supplement Appendix C, cited publication lines 1593--1599 | The binary level vector has endpoints `t_0 = 0` and `t_{M-1} = 1`; the repeated printed `t_0 = 1` is an endpoint typo. | The C.5 refinement setup has its unique intended endpoints. |
| Supplement Appendix B, cited publication lines 779--837 | Algorithm 1's outer midpoint is `j_{M-2} = (u + ell)/2`; both endpoint rates use the candidate vector, and the final helper call takes its target-rate argument. | The main-paper algorithm description determines one executable procedure. |
| Supplement Appendix C, cited publication lines 2206--2226 | The first endpoint rate is `-g_1 log(1-t_1)`, not `-g_1 log(t_1)`. | The local transcription slip does not alter the rate theorem. |
| Supplement Appendix C, cited publication lines 1143--1270 | Equal score levels do not make the complement error vanish.  The intended rate decomposition uses separated cross-level cells, equivalently erases within-cell ties. | The minimum adjacent-exponent conclusion is unchanged. |
| Supplement Appendix C, cited publication lines 1586--1597 | The stated lower bound should use `Omega(M^-3)` notation or an explicit positive-constant inequality, not `O(M^-3)`. | The subsequent quantitative lower bound supplies the intended direction. |
| Supplement Appendix C, cited publication lines 1081--1141 | The rate functions are not uniformly convergent on the full square near the diagonal.  The applicable argument is on separated cross-level cells (or uses a weighted essential-infimum bound). | The C.3/C.4 rate conclusions do not rely on a false global uniformity assertion. |
| Main paper Section 3 and Supplement Appendix C, cited publication lines 487--517 and 1328--1584 | The value-then-rate optimization needs its stated general nondecreasing matching-function construction, with a conventional resolution of an unspecified first-stage tie. | Theorem 3.1's advertised optimizer is retained. |
| Main paper Section 3 and Supplement Appendices B--C, cited publication lines 549--597, 779--837, and 2191--2381 | The algorithmic runtime argument needs an explicit gap bound connecting the discretization choice to the claimed joint dimension-and-accuracy runtime. | Theorem 3.2's algorithmic endpoint is retained. |
| Supplement Appendix B, cited publication lines 948--976 | The ranking-learning argument uses strict aggregate-score identifiability in addition to continuity. | The stated learning conclusion is retained under the condition used by the proof. |
| Supplement Appendix C, cited publication lines 1321--1325 | The two-endpoint objective is not jointly strictly convex on a diagonal with multiple minima.  What is used is interior continuity, diagonal zero, off-diagonal positivity, and strict coordinatewise separation. | The local wording is clarified without changing a named theorem. |
