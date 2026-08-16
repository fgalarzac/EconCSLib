# Final Validation Report: PRPKG24 Accuracy-Diversity
Updated: 2026-08-16

## 1. Human Verdict

**Formalized.** The paper's named theoretical results have closed proofs on
the source model, with the source correction and model clarifications stated below.
No paper-level caveat is recorded. Independent human review has not yet been
recorded.

## 2. Closeout Status

- Completion status: formalized.
- Scope: the paper's named definitions, theoretical results, and Equation (4)'s
  representation definition.
- Human review: not yet recorded.

## 3. Source and Scope

The source is [arXiv:2307.15142](https://arxiv.org/abs/2307.15142). The scope
includes Equation (4), Definitions 1--3, the named main-text results, and
Appendix Lemmas D.1--D.5. Simulations, numerical examples, figures, captions,
and other computational observations are not part of this formalization.

## 4. Researcher Summary of Checked Results

The formalized surface covers Equation (4)'s representation definition,
Definitions 1--3, Theorem 1, Corollaries 1 and 3, Theorems 2 and 3,
Propositions 2, 4, and 5, Lemma 1, and Appendix Lemmas D.1--D.5. Equation (3)
and other displayed formulas support these named results. The results retain
the selected-type probability law, the conditional finite experiment, exact
top-k semantics where required, the relevant product laws, and the clarified
Bernoulli models.

## 5. Remaining Boundaries and Gaps

The formalization does not claim an all-zero-weight extension, degenerate
Bernoulli endpoint conclusions, or the source's inconsistent iid formulation
of Theorem 2. These are explicit scope boundaries. Computational claims are
outside the formalized theoretical surface.

## 6. Additional Assumptions Beyond Paper

The all-coordinate gamma-share results require strictly positive type mass;
the source permits zero-mass types. Theorem 1(v) requires a nonnegative common
mean, and the Bernoulli results use their stated nondegeneracy domains.
Equation (4) is stated for a nonempty slate. These conditions are explicit in
the formalized statements.

## 7. Proof-Strategy Deviations

None.

## 8. Proof Tricks Worth Reusing

A positive probability-mass atom gives a direct positivity proof for the
finite normalizer in the gamma-share argument.

## 9. Generalizations, Conjectures, and Extensions

A supportwise treatment of zero-PMF coordinates could generalize the
all-coordinate share results, but it is not represented as an already-proved
extension. Any such extension should first specify whether coordinates with
zero selection probability are excluded or assigned a separate convention.

## 10. Source Clarifications and Exact Readings

Proposition 2 uses the factor-of-two finite coefficient. Theorem 2's
probability law is the independent rank-varying law specified by the displayed
model, rather than an iid law. The source anchors and row-level evidence for
these readings, including Appendix D, are in the
[paper statement map](audit/paper_statement_map.json).

## 11. Paper Issues or Caveats

None. The stated conditions and clarifications are formalization notes,
not status-bearing caveats.
