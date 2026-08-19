# Final Validation Report: LBG24 Spatial Underreporting

Updated: 2026-08-17

## 1. Human Verdict

Formalized.  The paper's named mathematical results and the mathematical
model components on which they rely have been checked against the pinned
source.  The calendar-time interpretation of Lemma 1 and Proposition 1, the
selected-start interpretation in Theorem 1, and the endpoint reading in
Appendix Theorem 2 are stated explicitly below so that the result does not
silently depend on a different observation model.

## 2. Closeout Status

- Completion status: formalized.
- Reviewed mathematical scope: the reporting model; Lemmas 1 and 2;
  Proposition 1; Theorem 1 and its Appendix Theorem 2 restatement; Eqs.
  (2)--(7), (30)--(34); and the two city-specific observation-end formulas.
- The source-first inventory contains 23 canonical mathematical targets.  Its
  empirical, simulation, and implementation descriptions are recorded as
  non-theorem material rather than represented as formal mathematical claims.

## 3. Source and Scope

The reviewed source is the published Nature Computational Science article,
with the paper-local extraction pinned by SHA-256
`2754d60d3304f72257c80a82c1bebbe416ff297ae27ddd13f4af9a0e114e3a6a`.
The [statement map](audit/paper_statement_map.json) gives the source locations
and the paper-facing proof routes.  The review is of the paper's mathematical
claims, not a claim that the empirical datasets or software reproduce every
reported result.

## 4. Researcher Summary of Checked Results

- Lemma 1's first-report probability and observed-rate formulas are checked.
  Under the settled calendar-time reading, observed incidents whose first
  reports fall in a time window form a homogeneous Poisson process at the
  displayed rate.
- Proposition 1's unit-window large-time law and its nonidentifiability point
  are checked: distinct reporting rates can be paired with latent incident
  rates that yield the same observed first-report process.
- Lemma 2 gives the exponential wait after the selected start.  Theorem 1 and
  Appendix Theorem 2 give the stated Poisson count likelihood factorization
  under the paper's rate-free start and causal endpoint conditions.
- The Poisson likelihood, MLE, regression, zero-inflated likelihood, and
  NYC/Chicago preprocessing formulas are checked at their stated domains.

## 5. Validity Boundaries

The result applies to the mathematical model presented in the paper.  It does
not certify empirical fit, causal validity of the city decision rules, or the
simulation outcomes.  The first-report result uses the paper's steady-state,
homogeneous incident-birth reading; it is not a statement about arbitrary
nonstationary arrival systems.

The paper's named-theory surface has no unresolved formalization boundary.
The source readings needed to make its shorthand precise are listed in the
next section and in the
[source-proof fidelity record](audit/source_proof_fidelity.json).

## 6. Source Clarifications and Explicit Model Readings

- **Calendar-time first reports.**  `N_observed(T)` counts incidents whose
  first report falls in the calendar interval `(0,T]`; it does not count only
  births in that interval that are eventually reported.  A stationary marked
  birth process is displaced by each retained incident's first-report delay.
- **Duration bridge.**  The displayed retention probability is read as the
  probability that the first report occurs before the incident's duration,
  conditional on that duration.  This is a pre-first-report condition only;
  it adds no restriction on later reports, incident resolution, or the
  endpoint policy.
- **Selected start and endpoint.**  The full stated selected-start version is
  used.  The endpoint may respond to the visible report history but not to an
  unseen future report gap or directly to the reporting-rate parameter.
- **MLE boundary.**  Eq. (3) is read on nonnegative reporting rates with
  positive total exposure.  If the total count is zero, the maximizer is zero.

These are clarifications of the source model's intended semantics, rather
than substitute claims about a different paper.

## 7. Source-Level Proof Notes

The Appendix multi-report calculation has two localized printed-algebra issues
in Eqs. (30) and (31).  The checked route uses the source-faithful first-gap
and residual-normalization readings documented in
[the Eq. (8) clarification](docs/EQ8_SOURCE_CLARIFICATION.md).  These notes
are limited to the displayed derivation; the likelihood theorem is checked
through its own stated causal observation model.

## 8. Proof Strategy Worth Reusing

- Specify the event-time object before applying Poisson thinning: a retained
  birth and a calendar-window first report are different random events.
- Treat a data-dependent observation end as one causal policy on the visible
  history, rather than as a collection of counterfactual endpoint clocks.
- State boundary conventions for likelihood optimization explicitly, including
  zero counts and positive exposure.

## 9. Generalizations and Extensions

The calendar-time proof is written for a stationary homogeneous incident-birth
model.  Extending it to nonstationary intensity, covariate-indexed marked
processes, or alternate first-report delay laws would require a corresponding
displacement theorem and an explicit revised observation model.

## 10. Review Materials

- [Dependency DAG](docs/DependencyDAG.pdf) presents the source-model premises
  and the checked paper claims.
- [Source-model readings](audit/source_proof_fidelity.json) gives the exact
  calendar-time, duration, endpoint, and MLE readings.
- [Source-proof fidelity record](audit/source_proof_fidelity.json) records the
  source-first comparison and repair dispositions.
- [Paper statement map](audit/paper_statement_map.json) is the detailed
  machine-readable source-to-proof index.
- [Human review packet](docs/HUMAN_REVIEW_PACKET.pdf) presents each source-map
  record, Lean statement, context-free translation, and saved statement
  judgment for row-by-row annotation. It is a review aid, not an independent
  human sign-off.

## 11. Caveats

No unresolved mathematical caveat remains within the reviewed named-theory
scope.  The explicit model readings in Section 6 are part of the formalized
statement and should accompany any reuse of the Lemma 1 or Proposition 1
conclusions.

## 12. Detailed Validation Record

The paper-facing review surface is
`papers/LBG24SpatialUnderreporting/PaperInterface.lean`.  The current
calendar-time Lemma 1 and Proposition 1 rows are
`lemma1_calendar_time_duration_source_observed_process`,
`proposition1_calendar_time_duration_source_count_lln`,
`proposition1_calendar_time_homogeneous_source_count_lln`, and
`proposition1_calendar_time_homogeneous_source_nonidentifiability`.

The direct audit records the source inventory, semantic comparison, model
conventions, and source-proof notes in
`audit/paper_statement_map.json` and `audit/source_proof_fidelity.json`.
Focused builds of the calendar displacement foundation, source-model bridge,
paper interface, and paper root passed on 2026-08-17.  The closure planner and
final receipt are issued only after the current source-record evidence is
frozen against this review surface.
