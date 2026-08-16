# Final Validation Report: LG21 Test-Optional Policies
Updated: 2026-08-16

## 1. Human Verdict

Formalized. The selected definitions and results through Theorem 4.4 are
covered under explicit equilibrium semantics. Theorem 3.2 uses the approved
corrected target stated in Section 10. Independent human review has not yet
been recorded.

## 2. Closeout Status

- Completion status: formalized.
- Normal scope: named definitions, Theorems 3.1--3.2, Lemma 4.1,
  Propositions 4.2--4.3, Definition 6, and Theorem 4.4.
- Simulations, figures, numerical examples, and non-theorem prose are outside
  this mathematical scope.

## 3. Source and Scope

The source is [Test-optional Policies: Overcoming Strategic Behavior and
Informational Gaps](https://arxiv.org/pdf/2107.08922). The reviewed scope is
the paper's named definitions, Theorems 3.1--3.2, Lemma 4.1, Propositions
4.2--4.3, Definition 6, and Theorem 4.4.

## 4. Researcher Summary of Checked Results

- Definition 1 separates test-taking from score reporting and specifies best
  responses and Bayesian-optimal estimates on attained positive-mass branches.
- Definitions 2--5 give the latent-skill, observable, demographic, and
  test-blankness properties of the output laws.
- Theorem 3.1 establishes the optional-reporting and report-required disclosure
  patterns and the three fairness failures.
- Theorem 3.2 gives the approved corrected target: deterministic output after
  a reported score, a common output on the no-report or no-take branch, and
  almost-everywhere test blankness under the stated fairness condition.
- Lemma 4.1 and Propositions 4.2--4.3 establish equilibrium behavior and
  unfairness for the three requirement protocols.
- Definition 6 and Theorem 4.4 give the resampling policy and its observable
  and demographic fairness.

## 5. Remaining Boundaries and Gaps

None.

## 6. Additional Assumptions Beyond Paper

The model makes two equilibrium conventions explicit: local recalibration for
Theorem 3.1 and positive-mass active-branch selection in Section 4. Null
branches are treated only up to measure zero; no off-path posterior is chosen.
These are operational readings of the source's equilibrium model, rather than
additional substantive premises.

## 7. Proof-Strategy Deviations

Theorem 3.1 states local recalibration explicitly and Section 4 states the
positive-mass active-branch rule explicitly. Gaussian conditional laws are used
only through almost-everywhere conclusions, so arbitrary null-fiber values do
not affect the results.

## 8. Proof Tricks Worth Reusing

- Separate attained positive-mass branches from arbitrary versions of
  conditional laws on null events.
- Keep the pre-score-taking decision distinct from the post-score-reporting
  decision.
- Analyze deviations using the information observed by the school rather than
  an unobserved latent-skill partition.

## 9. Generalizations, Conjectures, and Extensions

The positive-mass active-branch framework may be useful for other disclosure
models. Extending the posterior calculations beyond Gaussian signals would be
a separate result.

## 10. Source Clarifications and Exact Readings

The source anchors, clarified readings, and result-level effects are recorded
in [Source Clarifications](docs/SOURCE_CLARIFICATIONS.md).

- The Theorem 3.1 no-report mixture uses below-cutoff mass, rather than the
  printed reporting mass.
- The Theorem 3.1 cutoff-existence route uses proved Gaussian lower-tail
  continuity, denominator positivity, and endpoint signs; pointwise finiteness
  alone does not justify continuity of the parameterized improper integral.
- The Theorem 3.2 component uses deterministic reported-score output and an
  arbitrary common no-report or no-take output. Its final `demographic`
  reference is read as `observable`, consistently with the theorem's argument.
- Lemma 4.1 uses the affine inverse posterior threshold.
- Proposition 4.3 uses the unconditional precision comparison.

## 11. Paper Issues or Caveats

None.
