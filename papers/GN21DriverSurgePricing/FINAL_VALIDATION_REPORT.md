# Final Validation Report: Driver Surge Pricing

Updated: 2026-07-31

## 1. Human Verdict
Formalized for the recorded source model. Every named theoretical endpoint has
checked Lean coverage. Lemma 5 and Theorem 4 preserve their printed conclusions;
the a.e. null-set, finite endpoint-calculus, uniform-variation, and
empty-baseline readings are explicit source-model conventions rather than
corrected conclusions. Theorem 3 has a direct proof because the printed Lemma
9 route has a quantifier-scope gap; the stated theorem remains true. The source
definition rows remain support declarations rather than theorem evidence. No
independent human dashboard sign-off has been recorded.

## 2. Closeout Status
- Completion status: `formalized`; the current v10 receipt is complete.
- One-sentence recap: the direct T2 and T3 rows prove their source claims, and
  full Lemma 5 and Theorem 4 prove their printed conclusions under the explicit
  source-model readings required by the sequential variation route.
- Lean footprint: 180,771 paper-local Lean lines; `PaperInterface.lean` has
  3,749 lines; the review surface has 27 rows, including the visible source
  conditions used by the named-theory endpoints.
- Audit summary: source coverage has 14 covered, 2 conditional boundary; diagnostics: 1 selected source row without coverage evidence, 20 out-of-scope/orphan coverage rows excluded; statement LLM-as-judge has no rows; source conditions: 10 source condition; diagnostics: 32 orphan/stale statement-sidecar rows excluded, 17 configured rows without unambiguous current receipts; Lean-to-TeX has 22 row translations; assumption provenance has 10 source condition; diagnostics: 1 configured source condition without an unambiguous current receipt; source-record classification has 215 source condition, 4 recursively audited support, 2 non-propositional witness data, 16 semantic model review; source-record audit reports 27 source-record review rows, 181 boundary inputs, 24 conclusion dependencies, 61 recursive fields, 27 semantic-model records, 24 source-record-only unresolved conclusion dependencies, 0 recursion failures; review-surface audit review surface passed over 32 review rows; holistic source-first audit status is not inferred by this generator; DAG/source-json audit status is not inferred (see `docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`).
  elaborated semantic manifests, expanded model fields, and semantic routes.
  Item-level reuse requires the same anchored source content and a unique
  semantic match; Lean names and superficial raw spelling are navigation only.
- Open source targets: none. Independent human review remains release process
  work rather than a mathematical proof obligation.

## 3. Source and Scope
- Paper: *Driver Surge Pricing*.
- Authors: Nikhil Garg and Hamid Nazerzadeh.
- Source version: Management Science 2022 / arXiv v4, 2021.
- Public source: https://arxiv.org/abs/1905.07544
- Lean folder: `papers/GN21DriverSurgePricing`.
- Human-facing theorem file: `papers/GN21DriverSurgePricing/PaperInterface.lean`.
- Paper assumption file: `papers/GN21DriverSurgePricing/Assumptions.lean`.
- Holistic source audit: `papers/GN21DriverSurgePricing/docs/AGENT_SOURCE_AUDIT.md`.
- DAG artifacts: `papers/GN21DriverSurgePricing/docs/DependencyDAG.tex` and `papers/GN21DriverSurgePricing/docs/DependencyDAG.pdf`.

Scope: this report covers the paper's single-state and dynamic
incentive-compatibility definitions, threshold-policy and renewal-reward
material, Lemmas 1-10, Proposition 3.1, and Theorems 1-4. Lemma 5 and Theorem 4
are checked against their printed conclusions under the recorded source-model
readings. Definitions and the defined-reward carrier are retained as
source-model support rather than counted as independently proved conclusions.
Empirical or calibration material outside those named theoretical claims is
not part of the Lean theorem surface.

## 4. Researcher Summary of Checked Results
- The formalization checks the driver surge pricing model, incentive-compatibility definitions, renewal-reward route, and many derivative/reward-rate components.
- Theorem 2 is proved over the concrete measured multiplicative reward and the
  source open-policy domain. The proof derives the zero-mass endpoints,
  canonical cutoff domination, extended-cutoff continuity, and optimizer
  attainment from source-model primitives before invoking the all-optima shape
  route.
- Theorem 3 is proved on the source open-policy domain using the Appendix-D aggregate objective, including empty policies, with a fixed price selected from accept-all primitives before any deviation is considered.
- Lemma 5 proves all five endpoint-complete policy forms, compact existence,
  weak reward improvement, and strict improvement unless the original policy
  already has the selected form a.e.
- Theorem 4 preserves all six printed price-to-form cases, derives a
  compact source-open optimizer, and proves the selected a.e. forms for every
  optimizer.
- Zero-denominator totalized-division shortcuts are kept out of the named theorem rather than treated as economic caveats.

## 5. Remaining Boundaries and Gaps
There is no remaining mathematical proof, source-record, or semantic-receipt
queue. The current receipt records that the a.e. policy-equality convention
proves null-interval reward invariance but does not prove raw endpoint signs at
zero density. The finite endpoint-calculus, uniform-variation, and
empty-baseline conventions are separately expanded and source-anchored.
Release certification still needs independent human review and reviewer-identity
governance.

## 6. Additional Assumptions Beyond Paper
None. The a.e. equality, finite endpoint-calculus, uniform sequential
variation, better-than-empty seed, and continuous-probability regularities are
the approved formal rendering of the paper's source model. They are documented
under Source and Scope and in Section 13, not counted as rescue assumptions or
paper caveats.

## 7. Proof-Strategy Deviations
The Lean proof follows the paper's qualitative route, but makes two proof-level routes explicit where the source uses standard shorthand:

- Source route: Section 2.2 uses an informal renewal-reward limit argument.
  Lean route: the bridge is proved with IID cycles and strong-law wrappers.
  This makes the stochastic limit step an explicit checked theorem input.
- Source route: Theorem 1 treats threshold boundary behavior in prose. Lean
  route: the proof handles threshold-boundary atoms using one-sided
  dominated-convergence arguments. This avoids adding a hidden boundary-mass
  assumption.
- The printed Lemma 9 chooses a feasible price ratio after fixing a non-surge
  policy, whereas Theorem 3 needs one price to work uniformly over deviations.
  The checked proof fixes the structured price before optimizing and handles
  the target-rate range in two cases. The theorem's conclusion and policy
  domain are unchanged.

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

- Keep the historical Lemma 9 interval calculation diagnostic. The completed
  T3 proof instead fixes its Bellman price before the deviation policy and
  proves the aggregate envelope directly, avoiding the printed quantifier-order
  gap.

- Separate stochastic limit, algebraic reward-rate, and policy-shape work.
  Renewal-reward strong-law wrappers, CTMC scalar identities, and Lemma 5
  a.e. policy-form selectors each became tractable only after being isolated.

- For existential counterexamples under a continuous source law, build a
  concrete bounded-density continuous instance and reduce it to named
  aggregate primitives before doing strict inequalities. GN21's Theorem 2
  witness is a half-and-half mixture of uniforms on `[0.99,1.01]` and
  `[5.99,6.01]`; its component moments preserve the aggregate algebra without
  changing the source model to an atomic law.

## 9. Generalizations, Conjectures, and Extensions
No new generalization or conjecture is claimed by this closeout. Reusable
follow-up work is a general positive-denominator ratio API and shared two-state
CTMC reward accounting; neither is needed as an unproved premise for GN21.

## 10. Mathematical Typos or Other Fixes Suggested in the Source Paper
No mathematical typo or corrected conclusion is recorded for the named GN21
theory. The [Theorem 3 proof-route clarification](docs/THEOREM3_SOURCE_CLARIFICATION.md)
records the Lemma 9 quantifier issue and the direct two-case argument. The
post-formalization audit also records the intended source-model readings for
Appendix D's equality-up-to-measure-zero convention, the sequential variation
scope, and the compactification seed. The endpoint-sign realization is
deliberately documented as an authorized regularity rather than claimed as a
consequence of density-a.e. equality.

## 11. Paper Issues or Caveats
None. The following paragraphs state the current proof boundary; they are
formalization evidence, not paper caveats.

Theorem 2 is directly closed from primitive model assumptions in
`CutoffCanonicalization.lean` and `CutoffAttainment.lean`. The latter proves
continuity and compact maximization over the exact extended cutoff family; the
former supplies the policy-wise comparison from arbitrary source-open policies.
The denominator-valid domain is made explicit rather than relying on totalized
division outside the source proof route. Theorem 3 is directly proved from the
source primitives in `CTMCVerification.lean`; its proof does not depend on the
historical `surge_fixed_transfer_primitives` common-interval route. Full Lemma
5 and Theorem 4 are proved in `Lemma5Variational.lean`; their source-model
regularities are visible in transparent model packages and theorem binders,
without hiding an optimizer, bracket, policy form, or conclusion certificate.

## 12. Detailed Formalization Evidence
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

- Lemmas 4 and 6-10 are proved as components used by the dynamic theorems.
  This includes threshold uniqueness, the endpoint derivative formula, the
  quasi-convex/quasi-concave response facts, and the surge/non-surge derivative
  positivity lemmas used in Theorem 3.

- Theorem 2 is proved in two source-facing pieces: the structural
  multiplicative-policy shape result and an explicit instance with positive
  finite cutoff deviations in both states, proving that multiplicative pricing
  need not be incentive compatible.

- Lemma 5 is proved at `lemma5_full_variational_policy_forms`: finite endpoint
  normalization and compact maximization produce each of the five forms, while
  direct arbitrary-open variations prove strictness unless the source policy
  already has that form a.e.

- Theorem 4 is proved at
  `theorem4_full_structural_policy_forms_open_corrected`: statewise Lemma 5
  replacement feeds compact canonical-pair maximization, and strict replacement
  proves the every-optimizer a.e. clause for all six printed price cases.

- Theorem 3 is proved by selecting one structured Bellman price from accept-all
  primitives, proving a pointwise envelope for every source-open deviation,
  and integrating it into the Appendix-D aggregate objective. Strict loss on a
  positive rejected complement yields accept-all uniqueness up to null sets.

Other visible differences are source-domain choices or proof organization:
continuous policies are treated as measurable sets, source slope nonnegativity
is explicit in the T2 row, and Theorem 2's non-IC clause is witnessed by a
concrete measured bounded-density continuous instance. The earlier atomic
construction is retained only as historical/internal proof support and is not
the source-facing paper witness.

## 13. Paper Assumption Provenance

The eleven reusable source-domain declarations in
`papers/GN21DriverSurgePricing/Assumptions.lean` are tracked in
`audit/assumption_match_llm.json`; ten bind exact current receipts and one
remains unresolved. The source-model packages used by Lemma 5 and Theorem 4
remain transparent and are classified field by field by the source-record
audit.


Additional source-model regularities are recorded in the atom-complete
statement ledger. Lemma 6 itself no longer exposes pointwise
endpoint-density positivity as a premise of the derivative formula; Lean proves
the exact identity first and derives strict sign transfer only when density is
positive. Theorem 3's positive-denominator condition is the source domain of
the Appendix-D reward-rate formulas and remains visible rather than hidden in a
certificate.

<!-- BEGIN GENERATED ASSUMPTION PROVENANCE LEDGER -->
### Current Canonical Evidence
Generated from the configured source-condition surface and exact current statement digests in the canonical assumption-provenance sidecar. Model, agent, and automated checks are identified as such; no human review is inferred.

| Assumption declaration | Lean declaration | Source location / statement | Assumption validators | Comments |
| --- | --- | --- | --- | --- |
| Assumption affine single state parameter domain | `assumption_affine_single_state_parameter_domain` | - Affine single-state pricing parameter domain. | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | Proposition 3.1 states the affine single-state IC domain including positive arrival rate and 0 <= a <= m/lambda. Premise-level checks: 3 source condition |
| Assumption single state defined reward domain | `assumption_single_state_defined_reward_domain` | - Theorem 1 nontrivial-payout source-domain slice: one trip law has nonnegative payment per unit time on positive trips, finite accept-all mass, and positive accepted mass receiving a positive payout. | source condition; Agent check by Codex GN21 semantic-obligation closeout; 2026-07-15 | The source proof of Theorem 1 treats the nonnegative payment-rate branch and separates the trivial zero-payout case. The corrected one-measure declaration records finite accept-all mass and positive mass of accepted positive-payout trips for that branch. Premise-level checks: 3 source condition |
| Assumption dynamic time fraction denominators | `assumption_dynamic_time_fraction_denominators` | - Dynamic time-fraction denominators are nonzero. | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | The time-fraction denominators are immediate nonzero consequences of positive CTMC switching rates, nonnegative arrival mass, and the source Lemma 3 denominator formula. Premise-level checks: 2 source condition |
| Assumption switch rate domain | `assumption_switch_rate_domain` | - Dynamic-model CTMC source-domain slice: both displayed state-switch rates are positive. | source condition; Agent check by Codex GN21 semantic-obligation closeout; 2026-07-15 | The source dynamic model defines a two-state CTMC with a positive exponential transition rate in each direction. The corrected declaration exposes those two source conditions directly. Premise-level checks: 2 source condition |
| Assumption fixed response policy form conditions | `assumption_fixed_response_policy_form_conditions` | - Lemma 5 feasible-policy/optimality slice: the candidate policy is an open measurable subset of positive trip lengths, the response is measurable, and no measurable feasible policy has greater marginal reward. | source condition; Agent check by Codex GN21 semantic-obligation closeout; 2026-07-15 | Lemma 5 is explicitly about open measurable policies on positive trip lengths and its optimizer comparison ranges over feasible measurable policies. The formal row records that feasible-policy and marginal-reward optimality slice. Premise-level checks: 5 source condition |
| Assumption upper endpoint derivative domain | `assumption_upper_endpoint_derivative_domain` | - Lemma 6 endpoint derivative formula domain. | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | This row records the source-domain side conditions for the upper-endpoint derivative formula. The Lean theorem now proves the exact derivative identity without assuming positive density; density positivity appears only as the conditional premise of the strict sign-transfer conclusion. Premise-level checks: 8 source condition |
| Assumption affine response shape domains | `assumption_affine_response_shape_domains` | - Lemma 7/8 affine-response source-domain split: with positive slope and positive state weight, either the Lemma 7 branch has positive intercept and nonpositive Rj-Ri, or the Lemma 8 branch has negative intercept and nonnegative Rj-Ri; state-time denominators are nonzero. | source condition; Agent check by Codex GN21 semantic-obligation closeout; 2026-07-15 | Lemmas 7 and 8 state alternative affine sign and reward-gap regimes. The corrected declaration records their disjunction, plus the positive slope/state-weight and nonzero state-time conditions used in the source derivative calculation. Premise-level checks: 5 source condition |
| Assumption surge derivative source bounds | `assumption_surge_derivative_source_bounds` | - Lemma 9 surge-state derivative source-data formulas and bounds. | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | Lemma 9 supplies the surge pricing form, ratio bounds, and current-bound inequalities; the paper-facing wrapper constructs the Lemma 6 derivative data internally from interval-density primitives. Premise-level checks: 13 source condition |
| Assumption nonsurge derivative source bounds | `assumption_nonsurge_derivative_source_bounds` | - Lemma 10 non-surge derivative source-data formulas and bounds. | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | Lemma 10 supplies the non-surge pricing form, ratio bounds, and current-bound inequalities; the paper-facing wrapper constructs the Lemma 6 derivative data internally from interval-density primitives. Premise-level checks: 12 source condition |
| Assumption theorem3 source data domain | `assumption_theorem3_source_data_domain` | - Theorem 3 source-data domain for sequential current bounds. | source condition; Agent check by codex-gpt-5-semantic-audit; 2026-07-12 | Theorem 3 states the two-state R1 = rho * R2, R1 < R2, rho < 1, positive-switch, positive-arrival, and positive accept-all-measure source-data domain. Premise-level checks: 11 source condition |
| Assumption policy equalities modulo null sets | `assumption_policy_equalities_modulo_null_sets` | - Appendix D works with policies modulo the trip-length law. This is the source's explicit ``all policy equalities are up to measure 0'' convention, not a conclusion supplied by an optimizer package. | No completed assumption check recorded | None recorded |
<!-- END GENERATED ASSUMPTION PROVENANCE LEDGER -->

## 14. Displayed Formula Provenance

Displayed and source-defining formulas are tracked through the paper-facing rows in `PaperInterface.lean` and the current statement-match sidecars. This report pass found no standalone formula-provenance issue beyond any source notes already listed above.

<!-- BEGIN GENERATED FORMULA PROVENANCE LEDGER -->
### Current Canonical Evidence
Rows are selected from semantic `formula` and `equation` source-kind metadata within the configured semantic source-coverage scope, never from declaration names. Coverage and statement checks remain separate evidence lanes. Active coverage mode: named theoretical statements.

| Paper formula / subclaim | Lean declaration | Provenance | Validators | Comments |
| --- | --- | --- | --- | --- |
| None | `none` | None | None | No source-map row is canonically classified as a formula or equation. |
<!-- END GENERATED FORMULA PROVENANCE LEDGER -->

## 15. Library Lift Pass
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

- Bounded-density continuous-measure reductions: interval-restriction mass and
  moment simplification lemmas would make future source-faithful continuous
  counterexample constructions faster.

The GN21 paper-local definitions remain formula-explicit.  They are not opaque
aliases to generic library constants; instead the paper wrappers call the
library lemmas with `simpa` compatibility bridges.  This preserves the human
review surface and avoids destabilizing the long compiled proof.

## 16. DAG Audit
I rerendered `docs/DependencyDAG.pdf` from `docs/DependencyDAG.tex` after this pass and
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

## 17. Validation Checks
<!-- BEGIN GENERATED LLM-AS-JUDGE RESULTS -->
### LLM-as-Judge Results
- Source coverage (`audit/paper_coverage_llm.json`): 14 covered, 2 conditional boundary; diagnostics: 1 selected source row without coverage evidence, 20 out-of-scope/orphan coverage rows excluded.
- Statement match (`audit/statement_match_llm.json`): no rows; source conditions: 10 source condition; diagnostics: 32 orphan/stale statement-sidecar rows excluded, 17 configured rows without unambiguous current receipts.
- Lean-to-TeX translations (`audit/lean_to_tex_llm.json`): 22 row translations generated from Lean statements.
- Assumption provenance (`audit/assumption_match_llm.json`): 10 source condition; diagnostics: 1 configured source condition without an unambiguous current receipt.
- Source-record classification (`audit/source_record_match_llm.json`): 215 source condition, 4 recursively audited support, 2 non-propositional witness data, 16 semantic model review.
- Source-record structural audit (`audit/source_record_audit.json`): 27 source-record review rows, 181 boundary inputs, 24 conclusion dependencies, 61 recursive fields, 27 semantic-model records, 24 source-record-only unresolved conclusion dependencies, 0 recursion failures.
- Review-surface audit (`audit/review_surface_llm.json`): review surface passed over 32 review rows.
- Holistic source-first audit (`docs/AGENT_SOURCE_AUDIT.md`): status not inferred by this generator.
- DAG/source/source-json audit (`docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`): status not inferred by this generator.
<!-- END GENERATED LLM-AS-JUDGE RESULTS -->

### Human Review Status

`docs/AGENT_SOURCE_AUDIT.md` records an agent source audit for the
paper-interface rows. That audit checks that the Lean-facing rows correspond to
paper-facing source claims, but it is not human dashboard review.

The current configured review surface has 16 named theoretical rows and 11
source-condition rows. The a.e. endpoint packages are expanded support roots,
not extra theorem credit. No human dashboard sign-off has been recorded; that
is a review-process status, not a Lean proof gap.

The current receipt reports the a.e. convention and the raw finite
endpoint-sign realization separately. Density-a.e. equality is evidence for
null-interval reward invariance only; it is not evidence for a zero-density
endpoint sign.

### Verification Summary

The focused full-paper build succeeds:
`lake build GN21DriverSurgePricing` completed successfully on 2026-07-27.
`scripts/audit_conclusion_provenance.py` and
`scripts/audit_evidence_integrity.py` report zero
errors for GN21. The evidence check retains only the expected single-agent and
outstanding-human-review process warnings, not a mathematical or source-fidelity
gap.

The targeted closeout command is:

```bash
python3 scripts/audit_repository.py --paper GN21DriverSurgePricing
```

### Statement Translation Audit

Audit date: current semantic receipt, 2026-07-27.
Scope: the current `PaperInterface.lean` source surface, including the direct
T2 attainment row, direct T3 aggregate row, full Lemma 5 row, and Theorem 4
row.

Summary: the current pass uses the named-theory-only source inventory, explicit
model-convention routes, and expanded endpoint-package fields. These are agent
source-semantic judgments, not human or independent review certifications.

## 18. Paper Definitions Checked
<!-- lean-derived-definitions:start -->
### Lean-Derived Dashboard Definitions

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| def review_definition_single_state_ic | `review_definition_single_state_ic` | Single-state incentive compatibility: accept-all is weakly optimal among measurable feasible policies. |
| def review_definition_dynamic_ic | `review_definition_dynamic_ic` | Dynamic incentive compatibility: accept-all is weakly optimal among source-open feasible two-state policies. |
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
| abbrev review_lemma6_upper_endpoint_derivative_formula | `review_lemma6_upper_endpoint_derivative_formula` | - Lemma 6: upper-endpoint derivative formula. |
| abbrev review_lemma7_affine_positive_additive_response_quasi_convex | `review_lemma7_affine_positive_additive_response_quasi_convex` | - Lemma 7: positive-additive affine response is quasi-convex. |
| abbrev review_lemma8_affine_negative_additive_response_quasi_concave | `review_lemma8_affine_negative_additive_response_quasi_concave` | - Lemma 8: negative-additive affine response is quasi-concave. |
| abbrev review_lemma9_surge_derivative_positive_of_acceptAll_bounds | `review_lemma9_surge_derivative_positive_of_acceptAll_bounds` | - Lemma 9: surge-state derivative positivity under accept-all bounds. |
| abbrev review_lemma10_nonsurge_derivative_positive_of_acceptAll_bounds | `review_lemma10_nonsurge_derivative_positive_of_acceptAll_bounds` | - Lemma 10: non-surge-state derivative positivity under accept-all bounds. |
<!-- lean-derived-definitions:end -->

## 19. Named Theorem Statements Checked
<!-- lean-derived-statements:start -->
### Lean-Derived Dashboard Named Statements

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| theorem review_remark2_structured_scaled_earning_algebra | `review_remark2_structured_scaled_earning_algebra` | Direct source-aligned Remark 2 algebra. The Lean row derives switch-probability integrability internally from visible CTMC-rate, policy-domain, measurability, and trip-time-integrability premises. |
| theorem review_theorem2_multiplicative_policy_shape_source_claim | `review_theorem2_multiplicative_policy_shape_source_claim` | - Theorem 2: direct source-open optimizer existence and all-optima multiplicative cutoff shape, proved by canonicalization plus compact extended-cutoff maximization and the aggregate variation route. |
| theorem review_theorem2_multiplicative_positive_finite_cutoff_not_ic_both_states | `review_theorem2_multiplicative_positive_finite_cutoff_not_ic_both_states` | - Theorem 2: explicit multiplicative-pricing instance with positive finite cutoff deviations in both states, and hence measured dynamic non-IC. |
| theorem review_theorem3_structured_ic_source_claim | `review_theorem3_structured_ic_source_claim` | - Theorem 3: direct source-open structured pricing theorem with aggregate optimality and a.e. uniqueness from one accept-all-selected Bellman price. |
| theorem lemma5_full_variational_policy_forms | `lemma5_full_variational_policy_forms` | Lemma 5: all five endpoint-complete forms, compact existence, weak improvement, and strict improvement unless already in form a.e. The a.e. source-model convention proves null-interval reward invariance; the separately authorized finite endpoint-sign realization remains an expanded audit input. |
| theorem theorem4_full_structural_policy_forms_open_corrected | `theorem4_full_structural_policy_forms_open_corrected` | Theorem 4: all six price-to-form cases, compact source-open optimizer attainment, and every-optimizer a.e. forms under the explicit a.e. endpoint, uniform-variation, and empty-baseline source-model readings. |
<!-- lean-derived-statements:end -->

## 20. Paper-Facing Statement Validator Ledger

The raw sidecars carry a 2026-07-27 v10 receipt. Exact semantic projection
currently binds ten of eleven source-condition rows and none of the 16
statement rows; the remaining receipts are diagnostic-only.


The full row-level validator ledger is tracked in the JSON sidecars. Human
dashboard reviews and model/agent statement checks are separate provenance lanes;
this report does not change the human-only `human_review.reviewed_rows` counter.

<!-- BEGIN GENERATED STATEMENT VALIDATOR LEDGER -->
### Current Canonical Evidence
Independent human dashboard review: 0/27 rows. No human row-level approval is inferred. review surface passed; Agent check by Codex GN21 corrected-statement surface audit; 2026-07-16 Diagnostic-only evidence excluded from this paper-facing ledger: 32 unconfigured, stale, or ambiguous statement-sidecar rows.

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| Proposition 3.1: affine single-state pricing is incentive compatible. | `review_proposition3_1_affine_single_state_ic` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem 1: optimal single-state policies are threshold policies. | `review_theorem1_single_state_threshold_best_response` | No completed statement check recorded. No Lean translation recorded | None recorded |
| - Lemma 4: threshold optimizer uniqueness up to null sets. | `review_lemma4_single_state_threshold_uniqueness` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Lemma 1: under the dynamic renewal-cycle model, the sample-path cumulative total earnings divided by cumulative renewal-cycle time converges with probability one to the state-fraction-weighted state reward sum, represented by gn21MeasuredDynamicReward. | `review_lemma1_measured_dynamic_reward_decomposition` | No completed statement check recorded. No Lean translation recorded | None recorded |
| - Lemma 2: CTMC switch-probability formula. | `review_lemma2_switch_probability_formula` | No completed statement check recorded. Lean translation recorded; Agent check by Codex GN21 source-first closeout revalidation; 2026-07-16 | None recorded |
| Lemma 3: under the dynamic renewal-cycle model, the sample fraction of renewal-cycle time spent in state i converges with probability one to the displayed T,Q time-fraction formula, represented by gn21MeasuredTimeFraction. | `review_lemma3_measured_time_fraction_formula` | No completed statement check recorded. No Lean translation recorded | None recorded |
| - Lemma 6: upper-endpoint derivative formula. proves the exact endpoint derivative formula without assuming positive endpoint density; positive density is only the conditional premise for the strict sign-transfer corollary in the conclusion. | `review_lemma6_upper_endpoint_derivative_formula` | No completed statement check recorded. Lean translation recorded; Agent check by Codex GN21 source-first closeout revalidation; 2026-07-16 | None recorded |
| - Lemma 7: positive-additive affine response is quasi-convex. | `review_lemma7_affine_positive_additive_response_quasi_convex` | No completed statement check recorded. Lean translation recorded; Agent check by Codex GN21 source-first closeout revalidation; 2026-07-16 | None recorded |
| - Lemma 8: negative-additive affine response is quasi-concave. | `review_lemma8_affine_negative_additive_response_quasi_concave` | No completed statement check recorded. Lean translation recorded; Agent check by Codex GN21 source-first closeout revalidation; 2026-07-16 | None recorded |
| - Lemma 9: surge-state derivative positivity under accept-all bounds. | `review_lemma9_surge_derivative_positive_of_acceptAll_bounds` | No completed statement check recorded. No Lean translation recorded | None recorded |
| - Lemma 10: non-surge-state derivative positivity under accept-all bounds. | `review_lemma10_nonsurge_derivative_positive_of_acceptAll_bounds` | No completed statement check recorded. No Lean translation recorded | None recorded |
| - Theorem 2 (source.txt:560-579): for multiplicative pricing with nonnegative multipliers, an optimal source-open policy exists whose non-surge component rejects long trips up to a finite-or-infinite cutoff and whose surge component rejects short trips up to a finite-or-infinite cutoff, up to null sets. Every optimal source-open policy has those forms. The source model uses continuous probability trip laws, positi... | `review_theorem2_multiplicative_policy_shape_source_claim` | No completed statement check recorded. Lean translation recorded; Agent check by Codex GN21 semantic-obligation closeout; 2026-07-15 | None recorded |
| - Theorem 2: explicit multiplicative-pricing instance with positive finite cutoff deviations in both states, and hence measured dynamic non-IC. | `review_theorem2_multiplicative_positive_finite_cutoff_not_ic_both_states` | No completed statement check recorded. No Lean translation recorded | None recorded |
| - Theorem 3 (source.txt:704-720, 3944-4091): when the target-rate ratio lies in the displayed interval (C,1), there are structured prices w_i(tau) = m_i tau + z_i q_i_to_j(tau) with the stated nonnegativity constraints that attain the target accept-all state reward rates. Accept-all is optimal on the source open-policy domain, and every optimum agrees with accept-all up to null sets. | `review_theorem3_structured_ic_source_claim` | No completed statement check recorded. Lean translation recorded; Agent check by Codex GN21 semantic-obligation closeout; 2026-07-15 | None recorded |
| Lemma 5: for an objective on open measurable subsets of positive trip lengths with a continuous probability law, endpoint derivatives satisfying the stated continuity/sign-witness hypotheses, and a positive-mass starting policy above the empty-policy value, each of the five local response shapes (positive, strictly increasing, strictly decreasing, strictly quasi-convex, strictly quasi-concave) yields a no-worse po... | `lemma5_full_variational_policy_forms` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem 4: for the two-state source model with state 2 the surge state, there exists an open measurable optimal policy and every open measurable optimal policy has the price-case-specific interval form: non-surge positive additive prices reject long trips, negative additive prices accept a middle interval, and positive endpoint derivative cases accept all; surge negative additive prices reject short trips, positiv... | `theorem4_full_structural_policy_forms_open_corrected` | No completed statement check recorded. No Lean translation recorded | None recorded |
| - Affine single-state pricing parameter domain. | `assumption_affine_single_state_parameter_domain` | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | Proposition 3.1 states the affine single-state IC domain including positive arrival rate and 0 <= a <= m/lambda. |
| - Theorem 1 nontrivial-payout source-domain slice: one trip law has nonnegative payment per unit time on positive trips, finite accept-all mass, and positive accepted mass receiving a positive payout. | `assumption_single_state_defined_reward_domain` | source condition; Agent check by Codex GN21 semantic-obligation closeout; 2026-07-15 | The source proof of Theorem 1 treats the nonnegative payment-rate branch and separates the trivial zero-payout case. The corrected one-measure declaration records finite accept-all mass and positive mass of accepted positive-payout trips for that branch. |
| - Dynamic time-fraction denominators are nonzero. | `assumption_dynamic_time_fraction_denominators` | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | The time-fraction denominators are immediate nonzero consequences of positive CTMC switching rates, nonnegative arrival mass, and the source Lemma 3 denominator formula. |
| - Dynamic-model CTMC source-domain slice: both displayed state-switch rates are positive. | `assumption_switch_rate_domain` | source condition; Agent check by Codex GN21 semantic-obligation closeout; 2026-07-15 | The source dynamic model defines a two-state CTMC with a positive exponential transition rate in each direction. The corrected declaration exposes those two source conditions directly. |
| - Lemma 5 feasible-policy/optimality slice: the candidate policy is an open measurable subset of positive trip lengths, the response is measurable, and no measurable feasible policy has greater marginal reward. | `assumption_fixed_response_policy_form_conditions` | source condition; Agent check by Codex GN21 semantic-obligation closeout; 2026-07-15 | Lemma 5 is explicitly about open measurable policies on positive trip lengths and its optimizer comparison ranges over feasible measurable policies. The formal row records that feasible-policy and marginal-reward optimality slice. |
| - Lemma 6 endpoint derivative formula domain. | `assumption_upper_endpoint_derivative_domain` | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | This row records the source-domain side conditions for the upper-endpoint derivative formula. The Lean theorem now proves the exact derivative identity without assuming positive density; density positivity appears only as the conditional premise of the strict sign-transfer conclusion. |
| - Lemma 7/8 affine-response source-domain split: with positive slope and positive state weight, either the Lemma 7 branch has positive intercept and nonpositive Rj-Ri, or the Lemma 8 branch has negative intercept and nonnegative Rj-Ri; state-time denominators are nonzero. | `assumption_affine_response_shape_domains` | source condition; Agent check by Codex GN21 semantic-obligation closeout; 2026-07-15 | Lemmas 7 and 8 state alternative affine sign and reward-gap regimes. The corrected declaration records their disjunction, plus the positive slope/state-weight and nonzero state-time conditions used in the source derivative calculation. |
| - Lemma 9 surge-state derivative source-data formulas and bounds. | `assumption_surge_derivative_source_bounds` | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | Lemma 9 supplies the surge pricing form, ratio bounds, and current-bound inequalities; the paper-facing wrapper constructs the Lemma 6 derivative data internally from interval-density primitives. |
| - Lemma 10 non-surge derivative source-data formulas and bounds. | `assumption_nonsurge_derivative_source_bounds` | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | Lemma 10 supplies the non-surge pricing form, ratio bounds, and current-bound inequalities; the paper-facing wrapper constructs the Lemma 6 derivative data internally from interval-density primitives. |
| - Theorem 3 source-data domain for sequential current bounds. | `assumption_theorem3_source_data_domain` | source condition; Agent check by codex-gpt-5-semantic-audit; 2026-07-12 | Theorem 3 states the two-state R1 = rho * R2, R1 < R2, rho < 1, positive-switch, positive-arrival, and positive accept-all-measure source-data domain. |
| - Appendix D works with policies modulo the trip-length law. This is the source's explicit ``all policy equalities are up to measure 0'' convention, not a conclusion supplied by an optimizer package. | `assumption_policy_equalities_modulo_null_sets` | No completed source-condition check recorded | None recorded |
<!-- END GENERATED STATEMENT VALIDATOR LEDGER -->

## 21. Source-Coverage Audit Ledger

The canonical named-theory inventory contains 17 source statements: 14 have
recorded coverage, two retain conditional boundaries, and one has no completed
coverage receipt. Sixteen linked declaration references are present, but none
currently binds an exact semantic statement receipt. The full item-level
mapping and exact source locations are in `audit/paper_statement_map.json` and
the coverage sidecar.

<!-- BEGIN GENERATED SOURCE COVERAGE LEDGER -->
### Current Canonical Evidence
- Coverage scope: named theoretical statements.
- Source inventory: 17 source statements from `source.txt`.
- Coverage result: 2 conditional boundary, 14 covered, 1 no completed coverage check.
- Coverage review: coverage ledger recorded; Agent check by Codex GN21 corrected-statement coverage audit; 2026-07-16.
- Row-local statement checks: 0/16 linked row references have a completed canonical statement check; repeated links are counted per source row.

| Source statement | Linked Lean review rows | Coverage judgment | Row-local statement checks | Comments |
| --- | --- | --- | --- | --- |
| - Lemma 10: non-surge-state derivative positivity under accept-all bounds. | `review_lemma10_nonsurge_derivative_positive_of_acceptAll_bounds` | covered | `review_lemma10_nonsurge_derivative_positive_of_acceptAll_bounds`: no completed statement check | Source anchor source-facing theorem summary records the paper-facing item as: - Lemma 10: non-surge-state derivative positivity under accept-all bounds. The configured PaperInterface row states that same source claim on the review surface; this judgment is based on the anchored statement content and displayed Lean proposition. |
| Lemma 1: under the dynamic renewal-cycle model, the sample-path cumulative total earnings divided by cumulative renewal-cycle time converges with probability one to the state-fraction-weighted state reward sum, represented by gn21MeasuredDynamicReward. | `review_lemma1_measured_dynamic_reward_decomposition` | covered | `review_lemma1_measured_dynamic_reward_decomposition`: no completed statement check | Source anchor source-facing theorem summary records the paper-facing item as: - Lemma 1: dynamic reward decomposition. The configured PaperInterface row states that same source claim on the review surface; this judgment is based on the anchored statement content and displayed Lean proposition. |
| - Lemma 2: CTMC switch-probability formula. | `review_lemma2_switch_probability_formula` | covered | `review_lemma2_switch_probability_formula`: no completed statement check | Source anchor source-facing theorem summary records the paper-facing item as: - Lemma 2: CTMC switch-probability formula. The configured PaperInterface row states that same source claim on the review surface; this judgment is based on the anchored statement content and displayed Lean proposition. |
| Lemma 3: under the dynamic renewal-cycle model, the sample fraction of renewal-cycle time spent in state i converges with probability one to the displayed T,Q time-fraction formula, represented by gn21MeasuredTimeFraction. | `review_lemma3_measured_time_fraction_formula` | covered | `review_lemma3_measured_time_fraction_formula`: no completed statement check | Source anchor source-facing theorem summary records the paper-facing item as: - Lemma 3: state time-fraction formula. The configured PaperInterface row states that same source claim on the review surface; this judgment is based on the anchored statement content and displayed Lean proposition. |
| - Lemma 4: threshold optimizer uniqueness up to null sets. | `review_lemma4_single_state_threshold_uniqueness` | covered | `review_lemma4_single_state_threshold_uniqueness`: no completed statement check | Source anchor source-facing theorem summary records the paper-facing item as: - Lemma 4: threshold optimizer uniqueness up to null sets. The configured PaperInterface row states that same source claim on the review surface; this judgment is based on the anchored statement content and displayed Lean proposition. |
| - Lemma 6: upper-endpoint derivative formula. proves the exact endpoint derivative formula without assuming positive endpoint density; positive density is only the conditional premise for the strict sign-transfer corollary in the conclusion. | `review_lemma6_upper_endpoint_derivative_formula` | covered | `review_lemma6_upper_endpoint_derivative_formula`: no completed statement check | Source anchor source-facing theorem summary records the paper-facing item as: - Lemma 6: upper-endpoint derivative formula. proves the exact endpoint derivative formula without assuming positive endpoint density; positive density is only the conditional premise for the strict sign-transfer corollary in the conclusion. The configured PaperInterface row sta... |
| - Lemma 7: positive-additive affine response is quasi-convex. | `review_lemma7_affine_positive_additive_response_quasi_convex` | covered | `review_lemma7_affine_positive_additive_response_quasi_convex`: no completed statement check | Source anchor source-facing theorem summary records the paper-facing item as: - Lemma 7: positive-additive affine response is quasi-convex. The configured PaperInterface row states that same source claim on the review surface; this judgment is based on the anchored statement content and displayed Lean proposition. |
| - Lemma 8: negative-additive affine response is quasi-concave. | `review_lemma8_affine_negative_additive_response_quasi_concave` | covered | `review_lemma8_affine_negative_additive_response_quasi_concave`: no completed statement check | Source anchor source-facing theorem summary records the paper-facing item as: - Lemma 8: negative-additive affine response is quasi-concave. The configured PaperInterface row states that same source claim on the review surface; this judgment is based on the anchored statement content and displayed Lean proposition. |
| - Lemma 9: surge-state derivative positivity under accept-all bounds. | `review_lemma9_surge_derivative_positive_of_acceptAll_bounds` | covered | `review_lemma9_surge_derivative_positive_of_acceptAll_bounds`: no completed statement check | Source anchor source-facing theorem summary records the paper-facing item as: - Lemma 9: surge-state derivative positivity under accept-all bounds. The configured PaperInterface row states that same source claim on the review surface; this judgment is based on the anchored statement content and displayed Lean proposition. |
| Proposition 3.1: affine single-state pricing is incentive compatible. | `review_proposition3_1_affine_single_state_ic` | covered | `review_proposition3_1_affine_single_state_ic`: no completed statement check | Source anchor source-facing theorem summary records the paper-facing item as: - Proposition 3.1: affine single-state pricing is incentive compatible. The configured PaperInterface row states that same source claim on the review surface; this judgment is based on the anchored statement content and displayed Lean proposition. |
| Theorem 1: optimal single-state policies are threshold policies. | `review_theorem1_single_state_threshold_best_response` | covered | `review_theorem1_single_state_threshold_best_response`: no completed statement check | Source anchor source-facing theorem summary records the paper-facing item as: - Theorem 1: optimal single-state policies are threshold policies. The configured PaperInterface row states that same source claim on the review surface; this judgment is based on the anchored statement content and displayed Lean proposition. |
| - Theorem 2: explicit multiplicative-pricing instance with positive finite cutoff deviations in both states, and hence measured dynamic non-IC. | `review_theorem2_multiplicative_positive_finite_cutoff_not_ic_both_states` | covered | `review_theorem2_multiplicative_positive_finite_cutoff_not_ic_both_states`: no completed statement check | Source anchor source-facing theorem split records the paper-facing item as: - Theorem 2: explicit multiplicative-pricing instance with positive finite cutoff deviations in both states, and hence measured dynamic non-IC. The configured PaperInterface row states that same source claim on the review surface; this judgment is based on the anchored statement c... |
| Theorem 4: for the two-state source model with state 2 the surge state, there exists an open measurable optimal policy and every open measurable optimal policy has the price-case-specific interval form: non-surge positive additive prices reject long trips, negative additive prices accept a middle interval, and positive endpoint derivative cases accept all; surge negative additive prices reject short trips, positive additive prices re... | `theorem4_full_structural_policy_forms_open_corrected` | conditional boundary | `theorem4_full_structural_policy_forms_open_corrected`: no completed statement check | The printed Theorem 4 conclusion is covered by the full source-facing row. Its visible extra Lean premises are the current exact source-model convention receipts for a.e. policy equality, finite endpoint calculus, uniform sequential variation, and the nonempty baseline; no source conclusion is corrected or supplied as an input. |
| - Theorem 2 (source.txt:560-579): for multiplicative pricing with nonnegative multipliers, an optimal source-open policy exists whose non-surge component rejects long trips up to a finite-or-infinite cutoff and whose surge component rejects short trips up to a finite-or-infinite cutoff, up to null sets. Every optimal source-open policy has those forms. The source model uses continuous probability trip laws, positive arrival and CTMC... | `review_theorem2_multiplicative_policy_shape_source_claim` | covered | `review_theorem2_multiplicative_policy_shape_source_claim`: no completed statement check | Semantic source audit: the reviewed Lean statement has the exact optimizer-existence and all-optima cutoff conclusion of Theorem 2. Its nonnegative slopes, continuous normalized trip laws, positive rates, finite expectation domain, and surge dominance are explicit source-model/theorem premises, not packaged conclusions. |
| - Theorem 3 (source.txt:704-720, 3944-4091): when the target-rate ratio lies in the displayed interval (C,1), there are structured prices w_i(tau) = m_i tau + z_i q_i_to_j(tau) with the stated nonnegativity constraints that attain the target accept-all state reward rates. Accept-all is optimal on the source open-policy domain, and every optimum agrees with accept-all up to null sets. | `review_theorem3_structured_ic_source_claim` | covered | `review_theorem3_structured_ic_source_claim`: no completed statement check | Semantic source audit: the reviewed Lean statement constructs the structured prices, exact accept-all target rates, source-open aggregate optimality, and all-optima a.e. conclusion stated by Theorem 3. All technical premises are visible source-model or displayed target-ratio conditions. |
| Lemma 5: for an objective on open measurable subsets of positive trip lengths with a continuous probability law, endpoint derivatives satisfying the stated continuity/sign-witness hypotheses, and a positive-mass starting policy above the empty-policy value, each of the five local response shapes (positive, strictly increasing, strictly decreasing, strictly quasi-convex, strictly quasi-concave) yields a no-worse policy of the correspo... | `lemma5_full_variational_policy_forms` | conditional boundary | `lemma5_full_variational_policy_forms`: no completed statement check | The printed Lemma 5 conclusion is covered by the full source-facing row. Its visible extra Lean premises are the current exact source-model convention receipts for equality modulo the trip law and finite endpoint calculus; no source conclusion is corrected or supplied as an input. |
| Appendix D identifies policy equalities up to sets of trip-length measure zero and uses derivative-sign notation only away from points where the density is zero; Lemma 6's endpoint calculation displays the density factor in the derivative of the source aggregate quantities. | None recorded | no completed coverage check | No linked paper-facing row recorded | None recorded |
<!-- END GENERATED SOURCE COVERAGE LEDGER -->
