# Final Validation Report: GJ18 Informative Rating Systems
Updated: 2026-08-16

## 1. Human Verdict

Formalized. The finite-chain model uses the author-approved clarifications listed
in Section 6, including its iid state law and support-safe rate. These make the
governing model explicit without changing the paper's status. Independent human
review has not yet been recorded.

## 2. Closeout Status

- Completion status: formalized.
- Normal scope: the finite ordinal model, pairwise and uniform-ranking
  objectives, convergence results, and Theorem 1's rate.
- Model clarifications: the author-approved conditions are listed in Section 6.
- Human review: independent sign-off has not yet been recorded.

## 3. Source and Scope

The source is Garg and Johari, *Designing Informative Rating Systems: Evidence
from an Online Labor Market*. The governing target is an author-approved finite
ordinal iid model, not a claim that the archival recurrence alone derives a
product law. The public archival source is the [published Management Science
article](https://doi.org/10.1287/msom.2020.0921).

## 4. Researcher Summary of Checked Results

- The finite ordinal model fixes the type carrier, pair normalization,
  aggregate indexing, ordinal-tail comparisons, and iid floor-sample law.
- The pairwise and uniform-ranking objectives satisfy strict finite score
  separation, support-aware large-deviation bounds, and convergence to one.
- Theorem 1 has the stated exponential rate, including binary and
  larger-scale cases without terminal full rating support.

## 5. Remaining Boundaries and Gaps

None.

## 6. Additional Assumptions Beyond Paper

The author-approved model makes the following conditions explicit:

- at least two ordered seller types with a uniform prior and positive match
  rates;
- the stated aggregate count `floor(k * g(theta))`, rating-level order, and
  strict upper-tail comparisons;
- conditional iid ratings and independent seller histories at each horizon; and
- the valid adjacent-pair range, extended-real variational rate, and finite
  product argument used in the Appendix.

These are explicit governing-model conditions rather than claims that every
one is already stated in the archival version.

## 7. Proof-Strategy Deviations

The analysis makes the archive's informal recurrence-to-product-law step
explicit through an iid finite-product state law. It uses a finite-support
argument for the Appendix transfer and keeps the rate extended-real until
finiteness is established. These are model clarifications, not derivations
from the archival formulas alone.

## 8. Proof Tricks Worth Reusing

For finite ordinal models, prove score separation by selecting actual support
endpoints rather than manufacturing terminal full support. Keep large-deviation
objects extended-real through minimization, then prove a finite representative
only at the final theorem boundary. Make joint-law completion a visible model
field, not an inference from a suggestive recurrence name.

## 9. Generalizations, Conjectures, and Extensions

A future source revision could state the clarified theorem directly with an
extended-real rate. A real-only variant would need an explicit effective
support restriction and a proof that its rate is finite. A separate theorem
could derive the finite-chain model from a fully specified population/state
process rather than taking the iid horizon law as a governing clause.

## 10. Source Clarifications and Exact Readings

The aggregate summation endpoint, final valid adjacent-pair index, and
extended-real rate domain should be stated explicitly. The Appendix argument
should use the finite-support formulation rather than infer it from a
continuum/Laplace transfer. These are source-edit suggestions, not claims that
the pinned archive already states every clarified condition.

## 11. Paper Issues or Caveats

None. The source clarifications are stated explicitly in Sections 6 and 10.
