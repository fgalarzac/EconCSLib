# Final Validation Report: Driver Surge Pricing

Updated: 2026-07-03

## 1. Human Verdict
Formalized. The named driver-surge results are checked, with Theorem 3 stated
on the denominator-valid reward-rate domain used by Appendix D. No false main
theorem is reported; the only caveat is that zero-denominator totalized
division shortcuts are kept out of the named theorem. No human dashboard
sign-off has been recorded.

## 2. Closeout Status
- Completion status: formalized.
- One-sentence recap: The driver-surge IC definitions, renewal-reward route, and dynamic reward-rate theorem surface are formalized on the denominator-valid source domain.
- Lean footprint: 142,948 paper-local Lean LOC; `PaperInterface.lean` is 400 lines; 36 human-review declarations are exposed.
- Audit summary: source coverage has 34 covered, 2 conditional_boundary; statement LLM-as-judge has 34 matches, 2 mismatch; resolutions: 2 conditional_boundary; Lean-to-TeX has 26 row translations; assumption provenance has 10 paper_condition; source-record classification has 14 derived_consequence_record; source-record audit reports 34 review rows, 0 boundary inputs, 0 recursion failures; review-surface audit passes over 36 review rows; holistic source-first audit PASS; DAG/source-json audit PASS in `docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`.

## 3. Source and Scope
- Paper: *Driver Surge Pricing*.
- Authors: Nikhil Garg and Hamid Nazerzadeh.
- Source version: Management Science 2022 / arXiv v4, 2021.
- Lean folder: `papers/GN21DriverSurgePricing`.
- Human-facing theorem file: `papers/GN21DriverSurgePricing/PaperInterface.lean`.
- Paper assumption file: `papers/GN21DriverSurgePricing/Assumptions.lean`.
- Holistic source audit: `papers/GN21DriverSurgePricing/docs/AGENT_SOURCE_AUDIT.md`.
- DAG artifacts: `papers/GN21DriverSurgePricing/docs/DependencyDAG.tex` and `papers/GN21DriverSurgePricing/docs/DependencyDAG.pdf`.

Scope: this report covers the paper's single-state and dynamic incentive-compatibility definitions, threshold-policy and renewal-reward material, Lemmas 1-10, Proposition 3.1, Theorems 1-4, and the denominator-valid Theorem 3 endpoint. Empirical or calibration material outside those theoretical claims is not part of the Lean theorem surface.

## 4. Researcher Summary of Checked Results
- The formalization checks the driver surge pricing model, incentive-compatibility definitions, renewal-reward route, and dynamic reward-rate theorem surface.
- Theorem 3 is stated on the denominator-valid reward-rate domain used by the source proof.
- Zero-denominator totalized-division shortcuts are kept out of the named theorem rather than treated as economic caveats.

## 5. Remaining Boundaries and Gaps
None for the denominator-valid theorem surface formalized here.

## 6. Additional Assumptions Beyond Paper
None.

## 7. Proof-Strategy Deviations
The Lean proof follows the paper's qualitative route, but makes two proof-level routes explicit where the source uses standard shorthand:

- Source route: Section 2.2 uses an informal renewal-reward limit argument.
  Lean route: the bridge is proved with IID cycles and strong-law wrappers.
  This makes the stochastic limit step an explicit checked theorem input.
- Source route: Theorem 1 treats threshold boundary behavior in prose. Lean
  route: the proof handles threshold-boundary atoms using one-sided
  dominated-convergence arguments. This avoids adding a hidden boundary-mass
  assumption.

## 8. Proof Tricks Worth Reusing
- Work directly in the continuous/measure-theoretic model when the source proof
  is continuous.  The finite-support model was useful as support, but the paper
  closed only after the proof focused on measurable trip-length sets,
  integrals, and a.e. policy equality.

- State positive-denominator domains early.  The biggest avoidable delay was
  discovering that the paper's reward-rate notation assumes accepted-trip
  mass/time denominators are meaningful, while Lean's real division totalizes
  zero denominators.  This should have been surfaced earlier as a human-facing
  source-domain decision: prove the intended defined-reward theorem now,
  expose the denominator-valid domain, and only then decide whether an
  all-feasible zero-mass totalization strengthening is worth pursuing.

- Follow the paper's sequential Theorem 3 route.  The successful path first
  applies the surge Lemma 9 construction, then transports current bounds, then
  applies the non-surge Lemma 10 construction.  Symmetric all-at-once wrappers
  created stronger and sometimes false side obligations.

- Separate stochastic limit, algebraic reward-rate, and policy-shape work.
  Renewal-reward strong-law wrappers, CTMC scalar identities, and Lemma 5
  a.e. policy-form selectors each became tractable only after being isolated.

- For existential counterexamples, build a concrete measured atomic instance
  and reduce it to named aggregate primitives before doing strict inequalities.
  This avoided large symbolic expressions involving exponentials in the main
  proof path.

## 9. Mathematical Typos or Other Fixes Suggested in the Source Paper
None found.

## 10. Paper Issues or Caveats
No false main theorem is reported. The denominator-valid domain is made explicit rather than relying on totalized division outside the source proof route.

## 11. Detailed Formalization Evidence
- The paper's single-state and dynamic incentive-compatibility definitions are
  represented as measurable trip-policy optimization statements, including the
  threshold-policy notation and the positive-denominator dynamic reward domain.

- Section 2.2's renewal-reward claim is proved through an explicit IID cycle
  model: lifetime hourly earnings equal expected cycle reward divided by
  expected cycle length under the stated stochastic assumptions.

- Theorem 1 and Proposition 3.1 are proved for the single-state model.  Lean
  verifies the threshold best-response theorem and the affine-pricing
  incentive-compatibility condition `0 <= a <= m / lambda`.

- Lemmas 1-3 and Remarks 1, 3, and 4 are proved for the CTMC/dynamic reward
  formulas: reward decomposition, switch probabilities, time fractions, the
  small-time switch-rate limit, and the nonnegativity/monotonicity facts used
  later in Appendix D.

- Lemmas 4-10 are proved as the response-shape chain used by the dynamic
  theorems.  This includes threshold uniqueness, the fixed-response policy
  form, the endpoint derivative formula, the quasi-convex/quasi-concave
  response facts, and the surge/non-surge derivative positivity lemmas used in
  Theorem 3.

- Theorem 2 is proved in two source-facing pieces: the structural
  multiplicative-policy shape result and an explicit instance with positive
  finite cutoff deviations in both states, proving that multiplicative pricing
  need not be incentive compatible.

- Theorem 4 is proved at the measure-theoretic structural surface: optimal
  policies have representatives of the source's stated threshold/interval forms,
  up to null feasible-trip sets.

- Theorem 3 is proved through the paper proof path: first choose the
  surge-state structured price via Lemma 9, transport the resulting current
  bounds, then choose the non-surge price via Lemma 10.  The compact
  paper-facing statement constructs prices of the form
  `m_i tau + z_i q_{i->j}(tau)`, proves defined-reward dynamic incentive
  compatibility, and proves accept-all uniqueness up to null sets on the
  positive-denominator source domain used by the paper's reward-rate formulas.

Other visible differences are source-domain choices or proof organization:
continuous policies are treated as measurable sets, Theorem 3 is kept on the
denominator-valid reward-rate domain used by the source formulas, and Theorem
2's non-IC clause is witnessed by a concrete measured atomic instance.

## 12. Paper Assumption Provenance
Every paper-facing premise is routed through
`GN21DriverSurgePricing/Assumptions.lean` and checked by
`assumption_match_llm.json`. The assumption ledger separates source-domain
theorem conditions from remaining proof-route boundaries; the latter are not
counted as paper assumptions.

| Lean assumption/condition | Judgment | Source role |
| --- | --- | --- |
| `assumption_affine_single_state_parameter_domain` | paper condition | Proposition 3.1 affine single-state parameter domain. |
| `assumption_single_state_defined_reward_domain` | paper condition | Theorem 1/Lemma 4 single-state domain: nonnegative on-trip rates are stated in the Appendix C.2 proof table, finite accept-all mass is source-derived from the probability-measure domain, and the positive-payout-mass branch matches the source proof's nonzero-payout case. Lean derives positive accept-all expected payment from these premises. |
| `assumption_dynamic_time_fraction_denominators` | paper condition | Lemma 3 dynamic time-fraction denominators. |
| `assumption_switch_rate_domain` | paper condition | CTMC switch-rate positivity/nonzero total intensity. |
| `assumption_fixed_response_policy_form_conditions` | paper condition | Lemma 5 measurable optimal fixed-response policy condition. |
| `assumption_upper_endpoint_derivative_domain` | paper condition | Lemma 6 upper-endpoint derivative formula domain; the exact derivative identity no longer assumes positive endpoint density, and strict sign transfer is conditional on positive density inside the theorem conclusion. |
| `assumption_affine_response_shape_domains` | paper condition | Lemmas 7--8 affine response sign domains. |
| `assumption_surge_derivative_source_bounds` | paper condition | Lemma 9 surge-state ratio bounds and current-bound inequalities; the paper-facing wrapper constructs the Lemma 6 endpoint derivative data internally from interval-density primitives. |
| `assumption_nonsurge_derivative_source_bounds` | paper condition | Lemma 10 non-surge ratio bounds and current-bound inequalities; the paper-facing wrapper constructs the Lemma 6 endpoint derivative data internally from interval-density primitives. |
| `assumption_theorem3_source_data_domain` | paper condition | Theorem 3 positive values, arrivals, switches, and accept-all masses. |

Additional assumptions beyond the paper: none affecting the named paper
results. Lemma 6 no longer exposes pointwise endpoint-density positivity as a
premise of the derivative formula; Lean proves the exact derivative identity
first and only derives strict sign transfer conditionally when density is
positive.  Theorem 3's positive-denominator condition is the source domain of
the Appendix D reward-rate formulas, and is exposed in the defined-reward
statement rather than hidden as a certificate.

## 13. Displayed Formula Provenance
Displayed and source-defining formulas are tracked through the paper-facing rows in `PaperInterface.lean` and the current statement-match sidecars. This report pass found no standalone formula-provenance issue beyond any source notes already listed above.

## 14. Library Lift Pass
The post-closeout lift moved the reusable pieces that passed the "second paper"
test without disturbing the paper-facing GN21 definitions.

Lifted now:

- `EconCSLib.Foundations.Probability.ContinuousReward`: positive-real
  accepted-set mass, time, reward, renewal-reward, average-reward, and the
  zero accepted-time to zero accepted-mass bridge used by continuous
  trip-policy papers.

- `EconCSLib.Foundations.Optimization.Endpoint`: one-dimensional endpoint
  calculus from derivative signs, first/last-zero stopping lemmas, and
  one-sided local improvement/decrease steps for cutoff and interval-endpoint
  proofs.

Kept paper-local for now:

- Two-state CTMC reward accounting: state reward rates, exit weights, time
  fractions, positive-mass reward-rate bridges, and structured-price switch
  kernels should become reusable CTMC/renewal-reward infrastructure rather than
  GN21-only declarations.

- Positive-denominator defined-reward interfaces: papers with ratios should
  have a reusable API so source semantics do not depend on Lean's totalized
  real division at zero.

- Atomic continuous-measure reductions: weighted Dirac and finite atomic
  set-integral simplification lemmas would make future continuous
  counterexample constructions much faster.

The GN21 paper-local definitions remain formula-explicit.  They are not opaque
aliases to generic library constants; instead the paper wrappers call the
library lemmas with `simpa` compatibility bridges.  This preserves the human
review surface and avoids destabilizing the long compiled proof.

## 15. DAG Audit
I rerendered `DependencyDAG.pdf` from `DependencyDAG.tex` after this pass and
visually inspected the PDF.  The current DAG uses the shared preamble, has
visible spacing between nodes, and no arrow or label crosses through a node
body.

The DAG was made more paper-facing: the disconnected finite-MDP implementation
support box was removed, the appendix Remarks 1, 3, and 4 are now explicit, and
Theorem 2 is represented by one combined paper-facing box instead of separate
shape and counterexample boxes.  Optional zero-mass totalization is documented
in this report rather than shown as a named paper result in the DAG.  The
remaining boxes correspond to the paper-facing model, Section 2.2 renewal-reward bridge, named
lemmas/proposition/theorems, and the paper proof flow.
The DAG covers the source-result clusters recorded in the source inventory:
single-state and dynamic incentive-compatibility definitions, the renewal and
CTMC lemmas, Proposition 3.1, Theorems 1--4, grouped Lemmas 7--8 and 9--10,
and grouped Remarks 1, 3, and 4.

## 16. Validation Checks

<!-- BEGIN GENERATED LLM-AS-JUDGE RESULTS -->
### LLM-as-Judge Results
- Source coverage (`audit/paper_coverage_llm.json`): 34 covered, 2 conditional_boundary.
- Statement match (`audit/statement_match_llm.json`): 34 matches, 2 mismatch; resolutions: 2 conditional_boundary.
- Lean-to-TeX translations (`audit/lean_to_tex_llm.json`): 26 row translations generated from Lean statements.
- Assumption provenance (`audit/assumption_match_llm.json`): 10 paper_condition.
- Source-record classification (`audit/source_record_match_llm.json`): 14 derived_consequence_record.
- Source-record structural audit (`audit/source_record_audit.json`): 34 review rows, 0 boundary inputs, 0 recursion failures.
- Review-surface audit (`audit/review_surface_llm.json`): passes over 36 review rows.
- Holistic source-first audit (`docs/AGENT_SOURCE_AUDIT.md`): PASS.
- DAG/source/source-json audit (`docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`): PASS.
<!-- END GENERATED LLM-AS-JUDGE RESULTS -->

### Human Review Status

`SOURCE_AUDIT.md` records an agent source audit for the paper-interface rows.
That audit checks that the Lean-facing rows correspond to paper-facing source
claims, but it is not human dashboard review.

The current review surface has 36 human-review declarations. No human dashboard
sign-off has been recorded; that is a review-process status, not a Lean proof
gap.

### Verification Summary

The paper-local root module and final audit surfaces build successfully:
`GN21DriverSurgePricing`, `GN21DriverSurgePricing.PaperInterface`, and
`GN21DriverSurgePricing.PostPaperAudit`.  The dependency DAG renders, and the
GN21 paper folder has no remaining `sorry`, `admit`, `axiom`, or `by omega`
placeholders in `.lean` files.

The detailed declaration ledger lives in `PostPaperAudit.lean`; the durable
source-to-Lean checklist lives in `SOURCE_AUDIT.md`; and the concise
human-review theorem surface lives in `PaperInterface.lean`.

### Statement Translation Audit

Audit date: 2026-06-29.
Scope: current dashboard surface from `PaperInterface.lean`; the generated
LLM-as-judge block above is sourced from the tracked sidecars.

Summary: statement match has 34 matches, 2 mismatch; resolutions: 2 conditional_boundary; Lean-to-TeX has 26 row translations; assumption provenance has 10 paper_condition.
No separate stale manual validator table is maintained in this report.

## 17. Paper Definitions Checked
<!-- lean-derived-definitions:start -->
### Lean-Derived Dashboard Definitions

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| def review_definition_single_state_ic | `review_definition_single_state_ic` | Single-state incentive compatibility: accept-all is weakly optimal among measurable feasible policies. |
| def review_definition_dynamic_ic | `review_definition_dynamic_ic` | Dynamic incentive compatibility: accept-all is weakly optimal among feasible measurable two-state policies. |
| def review_definition_threshold_policy | `review_definition_threshold_policy` | Weak threshold policy condition: positive trip lengths are accepted iff payment per time is at least the cutoff. |
| def review_definition_dynamic_defined_reward | `review_definition_dynamic_defined_reward` | Denominator-valid domain for dynamic reward formulas: feasible measurable two-state policies with positive accepted-trip mass in each state. |
| abbrev review_section2_single_state_renewal_reward_iid_bridge | `review_section2_single_state_renewal_reward_iid_bridge` | - Section 2.2: IID renewal-reward bridge for the single-state formula. |
| abbrev review_proposition3_1_affine_single_state_ic | `review_proposition3_1_affine_single_state_ic` | - Proposition 3.1: affine single-state pricing is incentive compatible. |
| abbrev review_theorem1_single_state_threshold_best_response | `review_theorem1_single_state_threshold_best_response` | - Theorem 1: optimal single-state policies are threshold policies. |
| abbrev review_lemma4_single_state_threshold_uniqueness | `review_lemma4_single_state_threshold_uniqueness` | - Lemma 4: threshold optimizer uniqueness up to null sets. |
| abbrev review_lemma1_measured_dynamic_reward_decomposition | `review_lemma1_measured_dynamic_reward_decomposition` | - Lemma 1: dynamic reward decomposition. |
| abbrev review_lemma2_switch_probability_formula | `review_lemma2_switch_probability_formula` | - Lemma 2: CTMC switch-probability formula. |
| abbrev review_lemma3_measured_time_fraction_formula | `review_lemma3_measured_time_fraction_formula` | - Lemma 3: state time-fraction formula. |
| abbrev review_remark1_switch_probability_per_time_strictAntiOn | `review_remark1_switch_probability_per_time_strictAntiOn` | - Remark 1: switch probability per unit time is strictly decreasing. |
| abbrev review_remark3_switch_probability_per_time_tendsto_at_zero | `review_remark3_switch_probability_per_time_tendsto_at_zero` | - Remark 3: small-time switch probability per unit time tends to the switch rate. |
| abbrev review_remark4_switch_time_minus_switch_probability_nonneg | `review_remark4_switch_time_minus_switch_probability_nonneg` | - Remark 4: `lambda * t - q(t)` is nonnegative. |
| abbrev review_lemma5_fixed_response_policy_form | `review_lemma5_fixed_response_policy_form` | - Lemma 5: fixed-response feasible policy form almost everywhere. |
| abbrev review_lemma6_upper_endpoint_derivative_formula | `review_lemma6_upper_endpoint_derivative_formula` | - Lemma 6: upper-endpoint derivative formula. |
| abbrev review_lemma7_affine_positive_additive_response_quasi_convex | `review_lemma7_affine_positive_additive_response_quasi_convex` | - Lemma 7: positive-additive affine response is quasi-convex. |
| abbrev review_lemma8_affine_negative_additive_response_quasi_concave | `review_lemma8_affine_negative_additive_response_quasi_concave` | - Lemma 8: negative-additive affine response is quasi-concave. |
| abbrev review_lemma9_surge_derivative_positive_of_acceptAll_bounds | `review_lemma9_surge_derivative_positive_of_acceptAll_bounds` | - Lemma 9: surge-state derivative positivity under accept-all bounds. |
| abbrev review_lemma10_nonsurge_derivative_positive_of_acceptAll_bounds | `review_lemma10_nonsurge_derivative_positive_of_acceptAll_bounds` | - Lemma 10: non-surge-state derivative positivity under accept-all bounds. |
| abbrev review_theorem4_structural_policy_representatives | `review_theorem4_structural_policy_representatives` | - Theorem 4: structural representatives for optimal policies. |
<!-- lean-derived-definitions:end -->

## 18. Named Theorem Statements Checked
<!-- lean-derived-statements:start -->
### Lean-Derived Dashboard Named Statements

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| theorem review_theorem2_multiplicative_policy_shape_ae | `review_theorem2_multiplicative_policy_shape_ae` | - Theorem 2: multiplicative-pricing optimal-policy shape handoff. Lean states the policy-shape clause separately from the explicit non-IC counterexample because the paper's theorem combines a structural statement with an existential exam... |
| theorem review_theorem2_multiplicative_positive_finite_cutoff_not_ic_both_states | `review_theorem2_multiplicative_positive_finite_cutoff_not_ic_both_states` | - Theorem 2: explicit multiplicative-pricing instance with positive finite cutoff deviations in both states, and hence measured dynamic non-IC. |
| theorem review_theorem3_defined_reward_source_statement | `review_theorem3_defined_reward_source_statement` | matches. The Lean row matches the fully incentive-compatible accept-all clause of Theorem 3 on the source-domain where Appendix D reward-rate denominators are defined. Lean states this as defined-reward dynamic IC and a.e. uniqueness rather than as totalized real division at zero denominators. |
<!-- lean-derived-statements:end -->

## 19. Paper-Facing Statement Validator Ledger
Current source: `audit/statement_match_llm.json`, refreshed 2026-06-29, plus assumption provenance in `audit/assumption_match_llm.json`.

| Validator surface | Result |
| --- | --- |
| Statement match | 34 matches, 2 mismatch; resolutions: 2 conditional_boundary. |
| Lean-to-TeX drafts | 26 row translations generated from Lean statements. |
| Assumption provenance | 10 paper_condition. |
| Source coverage | 34 covered, 2 conditional_boundary. |

The full row-level validator ledger is tracked in the JSON sidecars. Human
dashboard reviews and model/agent statement checks are separate provenance lanes;
this report does not change the human-only `human_review.reviewed_rows` counter.
