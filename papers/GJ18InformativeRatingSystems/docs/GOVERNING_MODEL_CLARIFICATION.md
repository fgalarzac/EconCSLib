# Governing-Model Clarification

This note states the finite model used for the paper's formalized rating-system
results. It distinguishes that current mathematical model from an archival
presentation that leaves several ingredients implicit or ill-typed.

## Finite ordinal model

Seller types are ordered as `theta_0 < ... < theta_(M-1)` with `M >= 2` and a
uniform prior. Each type has a match rate `g(theta)` satisfying
`0 < g(theta) <= 1`, so that by horizon `k` it has `floor(k g(theta))` ratings.
Conditional on the seller type, ratings are independent and identically
distributed with the stated ordinal law; seller histories are independent. The
horizon-`k` state is the resulting finite product law.

The rating scale has at least two ordered levels with strictly increasing
scores. The displayed tail comparisons apply at their valid cutoffs; they do
not impose an impossible strict condition at the bottom cutoff.

## Theorem 1 reading

The Theorem 1 rate minimizes over the valid adjacent pairs `0 <= i <= M-2`.
Its rate function is extended-real inside the infimum, so an infeasible
threshold has infinite cost rather than an artificial real value. The resulting
minimum is finite and gives the stated real exponential rate.

Under this finite ordinal iid model, the advertised Theorem 1 conclusion is
the large-deviation rate for `1 - W_k`. This is a current governing-model
clarification, not an assertion that each clause was written explicitly in the
archival recurrence.
