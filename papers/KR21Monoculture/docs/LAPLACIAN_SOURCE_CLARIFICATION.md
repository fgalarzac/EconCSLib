# Appendix C Lemma 1: Laplacian Clarification

Appendix C Lemma 1 states a globally strict well-ordering property for
Laplacian noise. That strict statement is false: for separated ordered pairs,
the two products can be equal.

The correct global statement is the corresponding weak inequality. Strictness
holds on the local overlap region: if `a > b` and `c > d`, it requires
`b < c` and `d < a`.

For example, with the unnormalized kernel `f_x(y) = exp(-|y-x|)`, take
`a = 11`, `b = 10`, `c = 2`, and `d = 1`. Both products in the proposed strict
comparison equal `exp(-18)`.

The paper's named main-text results use the valid weak comparison together
with their later support and monotonicity arguments; they do not require the
false global strict form. This is therefore a source-proof deviation, not a
caveat about those results.
