# Final Validation Report: LMMS04 Fair Division
Updated: 2026-08-16

## 1. Human Verdict
Partially formalized. The envy and allocation results in Sections 2 and 4, and
the finite search and approximation support in Section 3, are covered. A full
PTAS/FPTAS result still needs a reusable fixed-dimension integer-programming
runtime theorem. Lemma 2.4 has a local endpoint-direction typo, not a caveat.
Independent human review has not yet been recorded.

## 2. Closeout Status
- Completion status: partially formalized.
- Covered scope: the Section 2 allocation results, Section 3 finite
  approximation support, and Section 4 truthfulness results.
- Remaining boundary: fixed-dimension integer-programming runtime analysis for
  the PTAS/FPTAS layer.
- Human review: independent sign-off has not yet been recorded.

## 3. Source and Scope
The source is Lipton, Markakis, Mossel, and Saberi, *On Approximately Fair
Allocations of Indivisible Goods*, EC 2004. This partial report covers the
Section 2 envy and allocation results, Section 3 approximation support, and
Section 4 truthfulness results. The final PTAS/FPTAS runtime layer of Theorem
3.3 remains outside the scope. The public source is
[the EC paper](https://doi.org/10.1145/988772.988792).

## 4. Researcher Summary of Checked Results
- Section 2 covers finite envy definitions, envy-cycle reduction, bounded-envy
  allocation, and the interval atom-bound argument.
- Section 3 covers adaptive-query and scheduling consequences, rounded search,
  and approximation-ratio transfer.
- Section 4 covers the truthfulness impossibility example and the uniform
  randomized mechanism.

## 5. Remaining Boundaries and Gaps
The PTAS/FPTAS runtime layer in Theorem 3.3 needs reusable fixed-dimension
integer-programming complexity infrastructure.

## 6. Additional Assumptions Beyond Paper
None.

## 7. Proof-Strategy Deviations
- Theorem 4.1 uses a smaller finite counterexample than the source exposition;
  it establishes the same impossibility result.
- Theorem 4.2 is represented through its finite inequality, rather than an
  asymptotic wrapper.

## 8. Proof Tricks Worth Reusing
- Separate finite approximation support from a machine-level runtime theorem so
  the partial boundary remains precise.
- Make endpoint choices explicit in interval partition arguments.

## 9. Generalizations, Conjectures, and Extensions

The envy-cycle, rounded-search, and truthfulness components may be reused in
other finite fair-division mechanisms. A fixed-dimension integer-programming
runtime theorem would extend this result.

## 10. Source Clarifications and Exact Readings
- Lemma 2.4 proof typo: the prose appears to say to choose the minimum endpoint whose prefix interval has value at most `alpha` for every player. To obtain progress and the stated finite partition, this should be read as a maximal/supremal endpoint choice.

## 11. Paper Issues or Caveats
The report is partial only because the PTAS/FPTAS runtime layer is open. Lemma
2.4's endpoint-direction typo is local and does not create a caveat.
