# Final Validation Report: MSVV07 AdWords
Updated: 2026-08-16

## 1. Human Verdict

Formalized. The finite AdWords model, the Balance guarantee and variants, the
Theorem 8 competitive-ratio analysis, the Theorem 9 lower bound, and the
Appendix counterexample are covered. Independent human review has not yet been
recorded.

## 2. Closeout Status

- Completion status: formalized.
- Normal scope: the AdWords model and Balance analysis, the Section 6 variants,
  Theorems 8--9, and Appendix A.
- Source-paper corrections: the finite Theorem 8 index and Appendix A's
  arithmetic and residual accounting are corrected without changing the
  substantive endpoints.
- Human review: independent sign-off has not yet been recorded.

## 3. Source and Scope

The source is Mehta, Saberi, Vazirani, and Vazirani, *AdWords and Generalized
Online Matching*, JACM 54(5), 2007, including Appendix A. The normal scope is
the paper's named definitions, lemmas, theorems, and stated model conditions;
Section 8's proposed algorithms are represented as proposals rather than given
performance guarantees that the source itself leaves open. The public source is
the [paper PDF](https://people.eecs.berkeley.edu/~vazirani/pubs/adwords.pdf).

## 4. Researcher Summary of Checked Results

- The finite AdWords model specifies budgets, bids, allocations, revenue, and
  the Balance rule.
- The Section 4--5 linear-program analysis proves the Balance guarantee, and
  Theorem 8 is established through its finite estimate and limiting form.
- Section 6's click-through-rate, availability, and slot variants retain the
  paper's accounting conclusions.
- Theorem 9 gives the finite permutation lower-bound construction and its
  harmonic asymptotic bound.
- Appendix A has a corrected execution and accounting proof of the intended
  strict counterexample. Section 8 proposals are retained without claiming the
  guarantees that the paper presents as open or heuristic.

## 5. Remaining Boundaries and Gaps

None in the selected named-theory scope. Section 8's performance questions and
heuristics remain open in the source itself, and the Appendix's limiting
formulation is not strengthened into a claim for every fixed positive
discretization.

## 6. Additional Assumptions Beyond Paper

None.

## 7. Proof-Strategy Deviations

None.

## 8. Proof Tricks Worth Reusing

- Establish a finite accounting estimate before taking a limiting
  competitive-ratio conclusion.
- Derive an execution's spend from its prior allocations rather than stipulating
  the claimed trajectory.
- Check both phase totals and exhaustion claims before relying on a printed
  numerical ratio.

## 9. Generalizations, Conjectures, and Extensions

Natural extensions are a quantified fixed-positive-discretization version of
the Appendix construction and analysis of the Section 8 switching and
replicated-RANKING proposals. Neither is needed for the paper's stated results.

## 10. Source Clarifications and Exact Readings

Theorem 8 has an off-by-one finite index: the displayed suffix sum and unspent
fraction use `k-i`, not `k-i+1`. This does not alter the limiting theorem.

Appendix A's printed phase totals sum to `0.6N`, not `0.62N`, and its claimed
phase-2 exhaustion is false. Correcting the remaining phase-3 allocation gives
the intended strict counterexample below `1-1/e`.

## 11. Paper Issues or Caveats

None. The Theorem 8 and Appendix corrections are local and preserve the paper's
substantive endpoints.
