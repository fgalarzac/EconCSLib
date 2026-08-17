# Appendix E Lemma 15 Source Clarification

Appendix E Lemma 15 gives formulas for an optimal solution of the paper's
equality-form linear program. Its printed center-pivot display omits one of
the two mirrored known-type contributions.

At the center pivot, `q_t = 1/2` and the complete equation gives

```text
lambda = 1 / (1 + L_t).
```

The printed expression is not equivalent. For example, with `n = 3`,
`beta = 2/5`, `q_t = 1/2`, and `L_t = 4/3`, the corrected value is `3/7`,
whereas the printed display gives `9/25`.

The noncenter coordinate formulas are unchanged. This is a localized Appendix
display correction; it does not alter a main-text result or the paper's
formalized status.
