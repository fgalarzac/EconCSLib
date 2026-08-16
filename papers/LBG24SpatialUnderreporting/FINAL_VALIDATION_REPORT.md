# Final Validation Report: LBG24 Spatial Underreporting
Updated: 2026-08-16

## 1. Human Verdict

Partially formalized. The Poisson, thinning, likelihood, and corrected Eq. (8)
mathematics are covered, but the paper's full observation law is not derived
from the stated source model. The remaining source-model boundaries are stated
in Section 5. Independent human review has not yet been recorded.

## 2. Closeout Status

- Completion status: partially formalized.
- Covered scope: Lemma 1, Proposition 1, the likelihood equations, the source
  reporting-process semantics, and the corrected Eq. (8) mathematics.
- The full Theorem 1 and Appendix Theorem 2 observation law remain open.

## 3. Source and Scope

The source is the [Nature Computational Science
article](https://www.nature.com/articles/s43588-023-00572-6). The reviewed
scope includes Lemma 1, Proposition 1, Theorem 1 and Appendix Theorem 2, the
likelihood equations, and the reporting-process model.

## 4. Researcher Summary of Checked Results

- Poisson and reporting-delay algebra, preprocessing minima, and regression and
  zero-inflated formulas are covered.
- A selected-start exponential waiting-tail result and a corrected stationary
  Palm factorization are covered.
- Finite causal traces, fixed-cap and resampled-clock models, and a
  birth-cohort thinning result are covered.
- The Eq. (30) and Eq. (31) algebra corrections are stated.

## 5. Remaining Boundaries and Gaps

The source does not derive the live-history conditional transition used in Eq.
(8), connect the corrected kernels to a single source endpoint and selected
start, or establish one observation model across rate values. Lemma 1 and
Proposition 1 also need a choice between birth-cohort counts and calendar-time
first-report counts, together with a duration/report-path survival law.

## 6. Additional Assumptions Beyond Paper

None. Eq. (3)'s parameter domain, positive total exposure, and zero-count
convention are ordinary regularity conditions; they do not resolve the
source-model boundaries in Section 5.

## 7. Proof-Strategy Deviations

Explicit Palm, fixed-cap, and resampled-clock models show which causal
conditions suffice. They are not asserted to follow from marginal independence
in the printed source model.

## 8. Proof Tricks Worth Reusing

- Separate birth-cohort thinning from calendar-time displacement.
- Use explicit causal endpoint kernels rather than marginal-independence
  shortcuts.

## 9. Generalizations, Conjectures, and Extensions

A two-sided stationary marked-displacement result would support the
calendar-time reading. A general causal stopping-endpoint kernel result would
also simplify the corrected Eq. (8) construction.

## 10. Source Clarifications and Exact Readings

Eq. (30) uses the first-gap term and Eq. (31) uses reciprocal residual
normalization. These source readings do not resolve the observation-model
ambiguity. Their source anchors and row-level evidence are in the
[paper statement map](audit/paper_statement_map.json).

## 11. Paper Issues or Caveats

The paper uses incompatible birth-cohort and calendar-time readings of the
observed count and does not state enough conditional structure for Eq. (8).
These are open source-model boundaries.
