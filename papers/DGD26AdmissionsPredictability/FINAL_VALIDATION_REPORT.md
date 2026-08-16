# Final Validation Report: Capacity Constraints Make Admissions Processes Less Predictable
Updated: 2026-08-16

## 1. Human Verdict

Formalized. The finite admissions model, threshold and rank-threshold
predictors, queue representations, Proposition 2 examples, and the
real-weight assignment application are covered. Independent human review has
not yet been recorded.

## 2. Closeout Status

- Completion status: formalized.
- Normal scope: the main choice model, Theorems 1--2, Proposition 2 examples,
  appendix support, and the linear-assignment application.
- Source-paper notes: local indexing, membership, and display typos, plus
  clarifications of the ordinary nondegenerate reading of several exact
  statements, do not change an advertised conclusion.
- Human review: independent sign-off has not yet been recorded.

## 3. Source and Scope

The source is *Capacity Constraints Make Admissions Processes Less
Predictable*, arXiv:2601.11513 / AAAI 2026. The normal scope covers its choice
model, named results, displayed application formulas, concrete program
examples, and appendix support. The public source is
[arXiv:2601.11513](https://arxiv.org/abs/2601.11513).

## 4. Researcher Summary of Checked Results

- Theorem 1 establishes the no-zero result, the substitutability/one-instability
  equivalence, and tight instability examples.
- Fixed thresholds have zero instability; rank thresholds satisfy the stated
  instability and variability bounds, including the exact-one construction.
- Theorem 2 gives the sequential-queue range and its single-order
  characterization under the source's nondegenerate reading.
- The four Proposition 2 program classes realize variability 1, 2, 3, and 6
  while retaining one-instability.
- The appendix choice, parity, and append/remove results, and the
  linear-assignment application with real tie-free weights, are covered.

## 5. Remaining Boundaries and Gaps

None in the selected mathematical scope. Empirical and simulation discussion
is outside the paper's theorem surface.

## 6. Additional Assumptions Beyond Paper

None.

## 7. Proof-Strategy Deviations

None.

## 8. Proof Tricks Worth Reusing

- Derive the parity bridge from capacity/cardinality accounting rather than
  accepting inserted-applicant nonselection as an extra premise.
- Represent pool-dependent ML claims through an explicit binary membership
  label and prove predictor equality pointwise; this makes the fixed/rank
  threshold consequences small extensional arguments.
- State realized variability with both an upper bound and a concrete witness.
  This prevents an at-most theorem from masquerading as an exact paper claim.
- For LAP counting, quotient slots by extensional equality of their induced
  strict orders and count the canonical image. This avoids confusing the raw
  number of slots with the number of distinct realized order classes.
- Generalizing the LAP weights from integers to reals required no change in the
  combinatorial proof architecture once the arithmetic assumptions were stated
  at the right abstraction level.

## 9. Generalizations, Conjectures, and Extensions

The real-weight assignment argument may extend to other ordered additive weight
domains. The paper's empirical, training, and simulation discussion makes no
additional theorem or runtime claim here.

## 10. Source Clarifications and Exact Readings

The formalized reading makes the following source conventions explicit:

- the no-zero clause needs positive capacity and a genuinely larger universe;
- the monotonicity/q-acceptance argument uses the one-extra-applicant
  formulation;
- the removable-set statement uses the intended cross-pool equality;
- several appendix lines contain local index, membership, parenthesis, or
  self-cardinality typos;
- strict-total-order completeness is read on distinct pairs;
- Theorem 2 and exact q-representative variability require the ordinary
  nondegenerate/minimal-representation reading;
- the source LAP world uses real-valued, tie-free weights and an optimizer
  satisfying its stated assignment conditions.

These conditions preserve every selected source endpoint. The source anchors
and exact readings are collected in
[Source Clarifications](docs/SOURCE_CLARIFICATIONS.md).

## 11. Paper Issues or Caveats

None.
