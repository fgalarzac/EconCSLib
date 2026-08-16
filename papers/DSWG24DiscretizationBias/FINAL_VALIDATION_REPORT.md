# Final Validation Report: DSWG24 Discretization Bias
Updated: 2026-08-16

## 1. Human Verdict

Formalized. The paper's discretization-bias definitions, main theorems, and
Appendix B.1 support are covered. Independent human review has not yet been
recorded.

## 2. Closeout Status

- Completion status: formalized.
- Normal scope: the main definitions and formulas, Theorems 1--2, and Appendix
  B.1's theoretical support.
- Human review: independent sign-off has not yet been recorded.

## 3. Source and Scope

The source is Dong, Schein, Wang, and Garg, *Addressing
Discretization-Induced Bias in Demographic Prediction*, FAccT 2024 / PNAS
Nexus 2025. The normal scope covers the main definitions, Equations (1)--(33),
Theorems 1--2, their stated model conditions, and Appendix B.1. Empirical
results and implementation code are outside the theorem scope. The public
source is [arXiv:2405.16762](https://arxiv.org/pdf/2405.16762).

## 4. Researcher Summary of Checked Results

- Theorem 1(i) identifies the worst-case no-information behavior; (ii) gives
  zero amplification bias for a perfect classifier on positive support under
  both stated reference distributions; and (iii) bounds argmax bias by
  predictive MAE and gives the stated tight binary example.
- Theorem 2(i) establishes the existence of an optimal joint rule for every
  weighted objective, (ii) identifies argmax as accuracy maximizing, and
  (iii) gives independent-rule Pareto uniqueness and the weighted-objective
  necessity result.
- Appendix B.1 supplies the finite-sample switch argument used in Theorem
  2(iii); the definitions and displayed formulas retain the paper's
  probability, support, posterior, and finite-domain conditions.

## 5. Remaining Boundaries and Gaps

None in the selected theoretical scope. Empirical results and implementation
code are outside the theorem surface.

## 6. Additional Assumptions Beyond Paper

None. Finiteness, measurability, probability, posterior, and support conditions
make the paper's model explicit; they do not supply a theorem conclusion.

## 7. Proof-Strategy Deviations

For Theorem 1, the paper sketches a continuous source-transformation argument.
That sketch leaves the measurable-transformation step and multiclass
`S_b`/`S_d` mass accounting underspecified. The checked proof establishes the
same bound directly from calibration; see [Source Clarifications](docs/SOURCE_CLARIFICATIONS.md)
for the source-route comparison. The theorem statement is unchanged.

## 8. Proof Tricks Worth Reusing

Expose the dataset-dependent reference family directly before lifting a
one-sample improvement into an expected-fidelity statement.

## 9. Generalizations, Conjectures, and Extensions

No additional generalization is claimed by this closeout.

## 10. Source Clarifications and Exact Readings

The main-text wording around Theorem 2(iii) is overbroad at `gamma = 1` if read
as making that value necessary for a rule that already agrees. Appendix B.1
proves the disagreement/improvement direction for `0 <= gamma < 1`. The
clarified reading preserves the substantive endpoint; anchors and its exact
scope are in [Source Clarifications](docs/SOURCE_CLARIFICATIONS.md).

## 11. Paper Issues or Caveats

None.
