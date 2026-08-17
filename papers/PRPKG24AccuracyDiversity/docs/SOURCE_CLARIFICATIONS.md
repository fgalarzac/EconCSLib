# Source Clarifications: Accuracy-Diversity

This note collects the current source-level readings for the paper's named
mathematical results. It does not publish the underlying paper source files.

## Proposition 2

The finite representation-error coefficient is `(2m+1)/n`, rather than the
printed `(m+1)/n`. The corrected finite bound still gives the paper's advertised
asymptotic square-root-share conclusion.

## Theorem 2

The displayed rank-dependent success schedule is interpreted as independent
rank-varying Bernoulli coordinates, not iid coordinates. The exact model and
its nondegenerate parameter conditions are in the companion [Theorem 2
probability-model clarification](THEOREM2_SOURCE_CLARIFICATION.md).

## Appendix D.1

The exponential-gap branch uses `B < 0` and `sigma > 0`; the logarithmic branch
has a unique maximum, not a minimum. The all-type conclusions use positive type
weights, while zero-weight coordinates require a separate supportwise reading.
The power and sublinear-power branches use the same positive-weight scope.

## Proposition 4 and Lemma D.5

The uniform profile attains the relevant infimum rather than being an element
of it. The finite integral retains its preference-weighted measure; full support
identifies the limiting rate, not each finite-sample integral. Lemma D.5 is a
concave maximization statement, with the corresponding regularity or a
derivative-free concavity argument.

These clarifications preserve the paper's named Proposition 4 and asymptotic
endpoints.
