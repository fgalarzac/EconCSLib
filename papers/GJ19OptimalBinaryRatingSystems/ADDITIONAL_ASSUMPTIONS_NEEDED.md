# GJ19 Source-Condition Audit

Updated 2026-06-28.

Closeout status: no additional public paper assumptions are needed for the
formalized GJ19 theorem surface. This file is retained as an agent-facing map
of proof-interface reducers that were useful during the final push.

The declarations in `Assumptions.lean` name source-condition packages and
alternative proof routes. They should not be summarized as caveats in
human-facing status unless a future source audit finds that a condition is
genuinely absent from the paper model.

## C.4 Rate Characterization

The formalized C.4 route uses the paper's source error sequence and explicit
model-regularity fields. Relevant checked declarations include:

- `paper_lemmaC4_appropriate_finite_levels_weighted_sourcePbarWbar_rate_certificate_of_selected_realization`
- `paper_lemmaC4_rawSourcePositiveSupportIntervalModel_finiteStep_iff_exists_positive_exponential_rate_of_sourcePbar_selected_realization`
- `paper_lemmaC4_global_monotone_nonfiniteStep_tieErasedWbar_has_zero_rate_of_theta_openPos_fields_raw_floorPkComplementError`
- `paper_lemmaC4_global_monotone_nonpiecewise_tieErasedWbar_has_zero_rate_of_positiveSupportInterval_fields_raw_floorPkComplementError`

Agent note: do not reintroduce a public status qualification here merely
because Lean exposes the source-condition fields explicitly. The source proof
uses these model facts in prose.

## Appendix B.1 Convergence

The paper-facing B.1 closeout route is:

- `paper_theoremB1_uniform_subsequence_principle_to_of_quantile_floor_tendstoUniformlyOn_geometric_mesh`

This route starts from the paper quantile-floor representation, finite
optimality, and uniform convergence of interval-quantile maps. Alternative
representative-transfer, anchor/mesh, and selector-coherence declarations
remain useful for future papers but are not public GJ19 status qualifications.

## Named Reducer Families

The following named families remain in `Assumptions.lean` as reusable audit
interfaces:

- representative-normalization routes for B.1;
- value-anchor and dyadic quantile-tracking routes for B.1;
- quantile-floor limit-tracking routes for B.1;
- positive-support interval packages for C.4;
- selected-source and pullback-source packages for C.4.

These names are stable proof-interface handles, not a statement that the GJ19
paper is missing assumptions.
