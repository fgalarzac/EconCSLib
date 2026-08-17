# Final Validation Report: DSWG24 Discretization Bias

Updated: 2026-07-31

## 1. Human Verdict

Formalized. This is not a `formalized with caveat` case. The two former gaps
were incomplete Lean coverage, and both now have exact source-shaped proofs.
There are no remaining mathematical formalization boundaries.

Independent human review has not been recorded.

## 2. Closeout Status

- Completion status: formalized.
- One-sentence recap: the former Theorem 1(ii) and Theorem 2(iii) gaps now have
  source-shaped proofs, and no named-theory boundary remains in `status.json`.

## 3. Source and Scope

- Paper: *Addressing Discretization-Induced Bias in Demographic Prediction*.
- Authors: Evan Dong, Aaron Schein, Yixin Wang, and Nikhil Garg.
- Source version: ACM FAccT 2024 / PNAS Nexus 2025 published version.

The audit covers the paper's main definitions, Equations (1)--(33), Theorems
1--2, their explicit model premises, and Appendix B.1 proof support. Empirical
results and implementation code are not formal theorem targets.

- Public source: [arXiv:2405.16762](https://arxiv.org/pdf/2405.16762).

Canonical audit source:

- path: `.audit_source/DSWG24DiscretizationBias.txt`;
- line count: 2,379;
- SHA-256: `2370832850d19fc3e0b74c5471316b099bcab9f958c268ffcd9de9d38ef55295`.

The older tracked extraction
`DSWG24DiscretizationBias.txt` has SHA-256
`ab554d513936d2b898b72f87e2f70674ce12737065b04591a5a00c371a6fb5cf`
and a different line layout. It was not overwritten.

## 4. Researcher Summary of Checked Results

### Theorem 1(ii)

`theorem1iiPriorReferenceZeroBiasSpec` and
`theorem1iiAggregateReferenceZeroBiasSpec` expose separate atomic contracts.
Their corresponding `*_on_support_spec` theorems prove zero bias for every
label from `perfectClassifierOnSupport`. The proof uses only positive joint
support; it does not assume one rule equals every label on the full product
type.

### Theorem 2(iii)

`theorem2iiiParetoOptimalAgreesArgmaxSpec` and
`theorem2iiiWeightedObjectiveMaximizerAgreesArgmaxSpec` use the exact
dataset-dependent `P_N^q` reference family. Their proof rows lift the source's
one-sample switch through a positive-mass iid event, evaluate expected fidelity
at `prefAt sample`, and conclude almost-sure argmax agreement. The auxiliary
`theorem2iii_source_randomized_augmented_endpoints` supplies the finite
realized-randomness specialization.

The weighted contract states `0 <= gamma < 1` and maximizer implies almost-sure
agreement. The main-text phrase “unless gamma=1 and D agrees” is overbroad if
read as making `gamma=1` necessary for an already agreeing rule; Appendix B.1
proves the disagreement/improvement direction formalized here. The audit keeps
this as a formalized source-wording note and does not claim Lean proves the
overbroad converse.

### Inventory and review surface

`audit/paper_statement_map.json` contains 96 items:

| Inventory role | Count |
| --- | ---: |
| Direct source targets | 39 |
| Source-premise declarations | 9 |
| Proof support | 48 |
| Open source targets | 0 |
| **Total** | **96** |

The 64-row interface consists of 55 theorem/definition rows and 9 assumption
declarations. The eight new reviewed rows are four transparent proposition
specifications and four proof theorems, so specifications do not masquerade as
proof evidence.

### Assumptions and proof strategy

No assumptions beyond the paper model are added. Finite-carrier,
equality-decision, measurability, simplex, probability-law, Bayes-posterior,
and expectation-linearity inputs make the source model explicit. The stronger
historical wrappers are auxiliary and do not discharge the repaired claims.

Theorem 1(ii) is proved by finite positive-mass atom identities. Theorem 2(iii)
uses an exact one-dataset policy modification and a positive-probability iid
lift. These are proof-engineering choices that preserve the source
quantification and terminal claims.

## 5. Remaining Boundaries and Gaps

None for the configured theoretical scope. Empirical results and implementation
code are not formal theorem targets.

## 6. Additional Assumptions Beyond Paper

None. Finite-carrier, equality-decision, measurability, simplex,
probability-law, Bayes-posterior, and expectation-linearity inputs make the
source model explicit; they do not supply a theorem conclusion.

## 7. Proof-Strategy Deviations

Theorem 1(ii) uses finite positive-mass atom identities. Theorem 2(iii) uses an
exact one-dataset policy modification and lifts it through a positive-mass iid
event. The stronger historical wrappers are auxiliary and receive no source
credit.

## 8. Proof Tricks Worth Reusing

Separate transparent atomic proposition specifications from proof theorems,
and expose the dataset-dependent reference family directly before lifting a
one-sample improvement into an expected-fidelity statement.

## 9. Generalizations, Conjectures, and Extensions

No additional generalization is claimed by this closeout.

## 10. Mathematical Typos or Other Fixes Suggested in the Source Paper

The main-text wording around Theorem 2(iii) is overbroad at `gamma = 1` if read
as making that value necessary for a rule that already agrees. Appendix B.1
proves the disagreement/improvement direction formalized here. The corrected
wording preserves the substantive endpoint and is a formalized source note.

## 11. Paper Issues or Caveats

None. The former gaps were incomplete Lean coverage, not unresolved paper
caveats.

## 12. Detailed Formalization Evidence

The source-first inventory contains 96 items: 39 direct source targets, nine
source-premise declarations, and 48 proof-support items, with no open target.
The 64-row interface contains 55 theorem or definition rows and nine assumption
rows. Four transparent proposition specifications and four corresponding proof
theorems close the repaired claims; specifications do not masquerade as proof
evidence. Lean has 27,227 paper-local lines, including the 1,330-line
`PaperInterface.lean`.

## 13. Paper Assumption Provenance

The nine configured assumption declarations record the paper's probability,
support, posterior, and finite-domain conditions. Their raw provenance receipts
do not bind the current cached semantic identities and remain diagnostic-only.
No additional premise supplies an agreement or optimality result.

<!-- BEGIN GENERATED ASSUMPTION PROVENANCE LEDGER -->
### Current Canonical Evidence
Generated from the configured source-condition surface and exact current statement digests in the canonical assumption-provenance sidecar. Model, agent, and automated checks are identified as such; no human review is inferred. Diagnostic-only evidence excluded from this ledger: 9 unconfigured, stale, or ambiguous source-condition sidecar rows.

| Assumption declaration | Lean declaration | Source location / statement | Assumption validators | Comments |
| --- | --- | --- | --- | --- |
| Assumption theorem1 no information case | `assumption_theorem1_no_information_case` | Theorem 1. Argmax bias depends on predictive uncertainty, i.e., how much information features x provide about the true class label. Consider calibrated classifier q and the argmax decision rule Dargmax . Let N > K and consider a reference distribution of either the aggregate posterior or the prior. Then, (i). Suppose x provides no information and q(y, x) = Pr(y) for all x, y. Then, amplification bias is maximized and all data points are classified as a plurality class: ( 1... | No completed assumption check recorded | None recorded |
| Assumption theorem1 plurality argmax class | `assumption_theorem1_plurality_argmax_class` | Theorem 1. Argmax bias depends on predictive uncertainty, i.e., how much information features x provide about the true class label. Consider calibrated classifier q and the argmax decision rule Dargmax . Let N > K and consider a reference distribution of either the aggregate posterior or the prior. Then, (i). Suppose x provides no information and q(y, x) = Pr(y) for all x, y. Then, amplification bias is maximized and all data points are classified as a plurality class: ( 1... | No completed assumption check recorded | None recorded |
| Assumption theorem1 perfect classifier | `assumption_theorem1_perfect_classifier` | Theorem 1. Argmax bias depends on predictive uncertainty, i.e., how much information features x provide about the true class label. Consider calibrated classifier q and the argmax decision rule Dargmax . Let N > K and consider a reference distribution of either the aggregate posterior or the prior. Then, (i). Suppose x provides no information and q(y, x) = Pr(y) for all x, y. Then, amplification bias is maximized and all data points are classified as a plurality class: ( 1... | No completed assumption check recorded | None recorded |
| Assumption theorem1 argmax rule measurable | `assumption_theorem1_argmax_rule_measurable` | Theorem 1. Argmax bias depends on predictive uncertainty, i.e., how much information features x provide about the true class label. Consider calibrated classifier q and the argmax decision rule Dargmax . Let N > K and consider a reference distribution of either the aggregate posterior or the prior. Then, (i). Suppose x provides no information and q(y, x) = Pr(y) for all x, y. Then, amplification bias is maximized and all data points are classified as a plurality class: ( 1... | No completed assumption check recorded | None recorded |
| Assumption theorem1 calibrated classifier | `assumption_theorem1_calibrated_classifier` | Theorem 1. Argmax bias depends on predictive uncertainty, i.e., how much information features x provide about the true class label. Consider calibrated classifier q and the argmax decision rule Dargmax . Let N > K and consider a reference distribution of either the aggregate posterior or the prior. Then, (i). Suppose x provides no information and q(y, x) = Pr(y) for all x, y. Then, amplification bias is maximized and all data points are classified as a plurality class: ( 1... | No completed assumption check recorded | None recorded |
| Assumption theorem2 at least two classes | `assumption_theorem2_at_least_two_classes` | Theorem 2. Consider Bayes optimal q, and N > K. For all F : (i). For every γ, pref there exists a joint decision-making rule that maximizes Oγ (D, q, pref ) in Equation (3). (ii). The argmax decision rule Dargmax maximizes O1 (D, q, pref ), i.e., is accuracy maximizing. (iii). Dargmax is the only Pareto optimal independent decision rule for non-trivial pref ∈ P. No independent decision rule D maximizes objective Oγ for any γ, unless γ = 1 and D agrees with Dargmax with pro... | No completed assumption check recorded | None recorded |
| Assumption theorem2 more rows than classes | `assumption_theorem2_more_rows_than_classes` | Theorem 2. Consider Bayes optimal q, and N > K. For all F : (i). For every γ, pref there exists a joint decision-making rule that maximizes Oγ (D, q, pref ) in Equation (3). (ii). The argmax decision rule Dargmax maximizes O1 (D, q, pref ), i.e., is accuracy maximizing. (iii). Dargmax is the only Pareto optimal independent decision rule for non-trivial pref ∈ P. No independent decision rule D maximizes objective Oγ for any γ, unless γ = 1 and D agrees with Dargmax with pro... | No completed assumption check recorded | None recorded |
| Assumption theorem2 positive sample count | `assumption_theorem2_positive_sample_count` | Theorem 2. Consider Bayes optimal q, and N > K. For all F : (i). For every γ, pref there exists a joint decision-making rule that maximizes Oγ (D, q, pref ) in Equation (3). (ii). The argmax decision rule Dargmax maximizes O1 (D, q, pref ), i.e., is accuracy maximizing. (iii). Dargmax is the only Pareto optimal independent decision rule for non-trivial pref ∈ P. No independent decision rule D maximizes objective Oγ for any γ, unless γ = 1 and D agrees with Dargmax with pro... | No completed assumption check recorded | None recorded |
| Assumption theorem2 reference nonnegative | `assumption_theorem2_reference_nonnegative` | Theorem 2. Consider Bayes optimal q, and N > K. For all F : (i). For every γ, pref there exists a joint decision-making rule that maximizes Oγ (D, q, pref ) in Equation (3). (ii). The argmax decision rule Dargmax maximizes O1 (D, q, pref ), i.e., is accuracy maximizing. (iii). Dargmax is the only Pareto optimal independent decision rule for non-trivial pref ∈ P. No independent decision rule D maximizes objective Oγ for any γ, unless γ = 1 and D agrees with Dargmax with pro... | No completed assumption check recorded | None recorded |
<!-- END GENERATED ASSUMPTION PROVENANCE LEDGER -->

## 14. Displayed Formula Provenance

The inventory covers Equations (1)--(33), including the positive-support bias
identities and the dataset-dependent `P_N^q` reference family. Formula rows are
linked to reviewed paper-facing declarations rather than credited through a
broad aggregate wrapper.

<!-- BEGIN GENERATED FORMULA PROVENANCE LEDGER -->
### Current Canonical Evidence
Rows are selected from semantic `formula` and `equation` source-kind metadata within the configured semantic source-coverage scope, never from declaration names. Coverage and statement checks remain separate evidence lanes. Scope metadata needs repair, so the full inventory is shown: paper_statement_map.json must explicitly set source_coverage_mode before a source-coverage closeout

| Paper formula / subclaim | Lean declaration | Provenance | Validators | Comments |
| --- | --- | --- | --- | --- |
| Equation (4): calibrated argmax class bias is bounded above by classifier MAE. | None recorded | support only. No linked paper-facing row recorded | support only; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This inventory item is a proof-region definition, intermediate equation, or local bridge used to audit the paper proof. It supports the listed reviewed or auxiliary Lean declarations but is not a standalone paper theorem target. |
| Equation (5): decompose the plurality-class prior mass over S_a, S_c, and S_e. | None recorded | out of scope. No linked paper-facing row recorded | out of scope; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This source item is an intermediate displayed proof equation with no standalone theorem claim; it remains pinned in the source inventory for proof traceability and does not require its own dashboard theorem row. |
| Equation (6): the plurality-class prior equals `a + c/K` in the reduced worst-case shape. | None recorded | out of scope. No linked paper-facing row recorded | out of scope; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This source item is an intermediate displayed proof equation with no standalone theorem claim; it remains pinned in the source inventory for proof traceability and does not require its own dashboard theorem row. |
| Equation (7): calibration at posterior score delta identifies the conditional true-label probability with delta. | None recorded | support only. No linked paper-facing row recorded | support only; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This inventory item is a proof-region definition, intermediate equation, or local bridge used to audit the paper proof. It supports the listed reviewed or auxiliary Lean declarations but is not a standalone paper theorem target. |
| Equation (8): classifier MAE as the joint integral of absolute posterior error at the realized label. | None recorded | support only. No linked paper-facing row recorded | support only; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This inventory item is a proof-region definition, intermediate equation, or local bridge used to audit the paper proof. It supports the listed reviewed or auxiliary Lean declarations but is not a standalone paper theorem target. |
| Equation (9): split MAE into the focal-label and nonfocal-label contributions. | None recorded | out of scope. No linked paper-facing row recorded | out of scope; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This source item is an intermediate displayed proof equation with no standalone theorem claim; it remains pinned in the source inventory for proof traceability and does not require its own dashboard theorem row. |
| Equation (10): evaluate the S_a contribution using the reduced region definitions. | None recorded | support only. No linked paper-facing row recorded | support only; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This inventory item is a proof-region definition, intermediate equation, or local bridge used to audit the paper proof. It supports the listed reviewed or auxiliary Lean declarations but is not a standalone paper theorem target. |
| Equation (11): evaluate the S_e contribution under a perfect nonfocal class. | None recorded | support only. No linked paper-facing row recorded | support only; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This inventory item is a proof-region definition, intermediate equation, or local bridge used to audit the paper proof. It supports the listed reviewed or auxiliary Lean declarations but is not a standalone paper theorem target. |
| Equation (12): collect the S_c contribution to MAE. | None recorded | support only. No linked paper-facing row recorded | support only; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This inventory item is a proof-region definition, intermediate equation, or local bridge used to audit the paper proof. It supports the listed reviewed or auxiliary Lean declarations but is not a standalone paper theorem target. |
| Equation (13): use calibration implications to reduce MAE to the middle-region mass term. | None recorded | support only. No linked paper-facing row recorded | support only; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This inventory item is a proof-region definition, intermediate equation, or local bridge used to audit the paper proof. It supports the listed reviewed or auxiliary Lean declarations but is not a standalone paper theorem target. |
| Equation (14): the argmax marginal share of the plurality class is `a+c`. | None recorded | out of scope. No linked paper-facing row recorded | out of scope; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This source item is an intermediate displayed proof equation with no standalone theorem claim; it remains pinned in the source inventory for proof traceability and does not require its own dashboard theorem row. |
| Equation (15): target aggregate-posterior preservation for the S_b transformation. | None recorded | out of scope. No linked paper-facing row recorded | out of scope; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This source item is an intermediate displayed proof equation with no standalone theorem claim; it remains pinned in the source inventory for proof traceability and does not require its own dashboard theorem row. |
| Equation (16): rewrite S_b aggregate preservation as equality of the changed-region integrals. | None recorded | out of scope. No linked paper-facing row recorded | out of scope; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This source item is an intermediate displayed proof equation with no standalone theorem claim; it remains pinned in the source inventory for proof traceability and does not require its own dashboard theorem row. |
| Equation (17): balance the lower and upper S_b score-mass changes. | None recorded | out of scope. No linked paper-facing row recorded | out of scope; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This source item is an intermediate displayed proof equation with no standalone theorem claim; it remains pinned in the source inventory for proof traceability and does not require its own dashboard theorem row. |
| Equation (18): express the MAE change for the first source transformation. | None recorded | out of scope. No linked paper-facing row recorded | out of scope; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This source item is an intermediate displayed proof equation with no standalone theorem claim; it remains pinned in the source inventory for proof traceability and does not require its own dashboard theorem row. |
| Equation (19): split the first transformation's MAE change by changed regions and labels. | None recorded | out of scope. No linked paper-facing row recorded | out of scope; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This source item is an intermediate displayed proof equation with no standalone theorem claim; it remains pinned in the source inventory for proof traceability and does not require its own dashboard theorem row. |
| Equation (20): reduce the first transformation's MAE delta to the balanced score-mass terms. | None recorded | out of scope. No linked paper-facing row recorded | out of scope; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This source item is an intermediate displayed proof equation with no standalone theorem claim; it remains pinned in the source inventory for proof traceability and does not require its own dashboard theorem row. |
| Equation (21): the balanced first transformation preserves MAE. | None recorded | out of scope. No linked paper-facing row recorded | out of scope; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This source item is an intermediate displayed proof equation with no standalone theorem claim; it remains pinned in the source inventory for proof traceability and does not require its own dashboard theorem row. |
| Equation (22): express the MAE change for the second source transformation. | None recorded | out of scope. No linked paper-facing row recorded | out of scope; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This source item is an intermediate displayed proof equation with no standalone theorem claim; it remains pinned in the source inventory for proof traceability and does not require its own dashboard theorem row. |
| Equation (23): split the second transformation's MAE change by changed regions and labels. | None recorded | out of scope. No linked paper-facing row recorded | out of scope; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This source item is an intermediate displayed proof equation with no standalone theorem claim; it remains pinned in the source inventory for proof traceability and does not require its own dashboard theorem row. |
| Equation (24): reduce the second transformation's MAE delta to balanced score-mass terms. | None recorded | out of scope. No linked paper-facing row recorded | out of scope; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This source item is an intermediate displayed proof equation with no standalone theorem claim; it remains pinned in the source inventory for proof traceability and does not require its own dashboard theorem row. |
| Equation (25): the balanced second transformation preserves MAE. | None recorded | out of scope. No linked paper-facing row recorded | out of scope; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This source item is an intermediate displayed proof equation with no standalone theorem claim; it remains pinned in the source inventory for proof traceability and does not require its own dashboard theorem row. |
| Equation (26): at gamma=1 the weighted objective is expected accuracy. | None recorded | support only. No linked paper-facing row recorded | support only; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This inventory item is a proof-region definition, intermediate equation, or local bridge used to audit the paper proof. It supports the listed reviewed or auxiliary Lean declarations but is not a standalone paper theorem target. |
| Equation (27): expand expected accuracy as expectation of finite-sample accuracy. | None recorded | support only. No linked paper-facing row recorded | support only; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This inventory item is a proof-region definition, intermediate equation, or local bridge used to audit the paper proof. It supports the listed reviewed or auxiliary Lean declarations but is not a standalone paper theorem target. |
| Equation (28): expand finite-sample accuracy into averaged correctness indicators. | None recorded | support only. No linked paper-facing row recorded | support only; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This inventory item is a proof-region definition, intermediate equation, or local bridge used to audit the paper proof. It supports the listed reviewed or auxiliary Lean declarations but is not a standalone paper theorem target. |
| Equation (29): apply the tower property conditional on the observed feature dataset. | None recorded | out of scope. No linked paper-facing row recorded | out of scope; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This source item is an intermediate displayed proof equation with no standalone theorem claim; it remains pinned in the source inventory for proof traceability and does not require its own dashboard theorem row. |
| Equation (30): use independent sampling to separate row-wise conditional expectations. | None recorded | support only. No linked paper-facing row recorded | support only; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This inventory item is a proof-region definition, intermediate equation, or local bridge used to audit the paper proof. It supports the listed reviewed or auxiliary Lean declarations but is not a standalone paper theorem target. |
| Equation (31): replace each conditional correctness probability by the Bayes posterior score. | None recorded | support only. No linked paper-facing row recorded | support only; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This inventory item is a proof-region definition, intermediate equation, or local bridge used to audit the paper proof. It supports the listed reviewed or auxiliary Lean declarations but is not a standalone paper theorem target. |
| Equation (32): row-wise posterior scores are weakly increased by the tie-broken argmax choice. | None recorded | support only. No linked paper-facing row recorded | support only; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This inventory item is a proof-region definition, intermediate equation, or local bridge used to audit the paper proof. It supports the listed reviewed or auxiliary Lean declarations but is not a standalone paper theorem target. |
| Equation (33): identify the resulting upper bound with the argmax rule's gamma=1 objective. | None recorded | support only. No linked paper-facing row recorded | support only; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This inventory item is a proof-region definition, intermediate equation, or local bridge used to audit the paper proof. It supports the listed reviewed or auxiliary Lean declarations but is not a standalone paper theorem target. |
| Finite observed-label accuracy is `acc(y_1:N, yhat_1:N) = (1/N) sum_i 1[yhat_i = y_i]`. | `accuracy` | covered. `accuracy`: no completed statement check | covered; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| Equation (1) scores a decision vector by gamma times average posterior score plus (1-gamma) times fidelity to the supplied reference. | `equation1Objective` | covered. `equation1Objective`: no completed statement check | covered; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| Equation (2) defines ACC_N(D,q) as expected finite-sample 0-1 accuracy over sampled datasets and rule randomness. | `equation2ExpectedAccuracy` | covered. `equation2ExpectedAccuracy`: no completed statement check | covered; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| FID_N(D,q,pref) is expected per-dataset fidelity, with the reference allowed to depend on the observed dataset. | `expectedFidelityAt` | covered. `expectedFidelityAt`: no completed statement check | covered; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| BIAS_N(y,D,q,pref) is expected per-dataset class bias under the sampled-data law and rule randomness. | `expectedBiasAt` | covered. `expectedBiasAt`: no completed statement check | covered; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| Equation (3) is `O_N^gamma = gamma ACC_N + (1-gamma) FID_N`. | `equation3ExpectedObjective` | covered. `equation3ExpectedObjective`: no completed statement check | covered; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| - Prior class probability `Pr(y)`. | `prior` | covered. `prior`: no completed statement check | covered; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| - Marginal label share `\hat p_marg(y) = (1/N) sum_i 1[\hat y_i = y]`. | `marginalLabelShare` | covered. `marginalLabelShare`: no completed statement check | covered; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| - Aggregate posterior `p_agg^q(y) = (1/N) sum_i q(y,x_i)`. | `aggregatePosterior` | covered. `aggregatePosterior`: no completed statement check | covered; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| - Bias `bias(y, \hat y, p_ref) = \hat p_marg(y) - p_ref(y)`. | `bias` | covered. `bias`: no completed statement check | covered; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| - Distributional fidelity `fid(p_ref, \hat y) = -sum_y \|bias(y,\hat y,p_ref)\|`. | `fidelity` | covered. `fidelity`: no completed statement check | covered; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| - Predictive MAE for Bayes posterior scores: `E_X sum_y q(y,x)(1-q(y,x))`. | `classifierMAE` | covered. `classifierMAE`: no completed statement check | covered; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| - Continuous marginal label share: `∫ x, 1[rule x = y] dμ(x)`. | `continuousMarginalLabelShare` | covered. `continuousMarginalLabelShare`: no completed statement check | covered; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This source-visible proof definition, formula, or named theorem endpoint is exposed by exactly one reviewed row with a current v10 semantic ledger; its proof-support inventory role does not reduce the coverage of that source-facing row. |
| - Continuous aggregate posterior reference: `∫ x, q x y dμ(x)`. | `continuousAggregatePosterior` | covered. `continuousAggregatePosterior`: no completed statement check | covered; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This source-visible proof definition, formula, or named theorem endpoint is exposed by exactly one reviewed row with a current v10 semantic ledger; its proof-support inventory role does not reduce the coverage of that source-facing row. |
| - Continuous bias relative to a supplied reference distribution. | `continuousBias` | covered. `continuousBias`: no completed statement check | covered; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This source-visible proof definition, formula, or named theorem endpoint is exposed by exactly one reviewed row with a current v10 semantic ledger; its proof-support inventory role does not reduce the coverage of that source-facing row. |
| - Continuous aggregate-posterior bias. | `continuousAggregateBias` | covered. `continuousAggregateBias`: no completed statement check | covered; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This source-visible proof definition, formula, or named theorem endpoint is exposed by exactly one reviewed row with a current v10 semantic ledger; its proof-support inventory role does not reduce the coverage of that source-facing row. |
| - Continuous predictive MAE. | `continuousClassifierMAE` | covered. `continuousClassifierMAE`: no completed statement check | covered; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This source-visible proof definition, formula, or named theorem endpoint is exposed by exactly one reviewed row with a current v10 semantic ledger; its proof-support inventory role does not reduce the coverage of that source-facing row. |
| - Joint prior-reference bias for Theorem 1's continuous statement. | `continuousJointPriorBias` | covered. `continuousJointPriorBias`: no completed statement check | covered; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This source-visible proof definition, formula, or named theorem endpoint is exposed by exactly one reviewed row with a current v10 semantic ledger; its proof-support inventory role does not reduce the coverage of that source-facing row. |
| - Joint predictive MAE for Theorem 1's continuous statement. | `continuousJointClassifierMAE` | covered. `continuousJointClassifierMAE`: no completed statement check | covered; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | This source-visible proof definition, formula, or named theorem endpoint is exposed by exactly one reviewed row with a current v10 semantic ledger; its proof-support inventory role does not reduce the coverage of that source-facing row. |
| - Paper objective `O_N^gamma` for one observed dataset: `γ` times average posterior score plus `(1 - γ)` times the fidelity term. | `objective` | covered. `objective`: no completed statement check | covered; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| - Expected paper objective using true-label accuracy plus expected fidelity. | `expectedObjective` | covered. `expectedObjective`: no completed statement check | covered; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-18 | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
<!-- END GENERATED FORMULA PROVENANCE LEDGER -->

## 15. Library Lift Pass

Reusable finite probability and iid-event infrastructure remains shared. The
paper-local policy modification and exact reference-family statements stay in
this paper. Recursive provenance found no unresolved conclusion dependency.

## 16. DAG Audit

`docs/DependencyDAG.pdf` was rebuilt from the current TeX source and visually
inspected. It records the two repaired theorem routes and their source-model
dependencies.

## 17. Validation Checks
<!-- BEGIN GENERATED LLM-AS-JUDGE RESULTS -->
### LLM-as-Judge Results
- Source coverage (`audit/paper_coverage_llm.json`): 62 covered, 16 out of scope, 18 support only; diagnostics: full inventory shown because paper_statement_map.json must explicitly set source_coverage_mode before a source-coverage closeout.
- Statement match (`audit/statement_match_llm.json`): no rows; diagnostics: 64 orphan/stale statement-sidecar rows excluded, 9 orphan/stale source-condition sidecar rows excluded, 64 configured rows without unambiguous current receipts.
- Lean-to-TeX translations (`audit/lean_to_tex_llm.json`): 55 row translations generated from Lean statements.
- Assumption provenance (`audit/assumption_match_llm.json`): no current configured source-condition receipts; diagnostics: 9 unconfigured, stale, or ambiguous source-condition sidecar rows excluded, 9 configured source conditions without unambiguous current receipts.
- Source-record classification (`audit/source_record_match_llm.json`): 69 source condition, 11 non-propositional witness data.
- Source-record structural audit (`audit/source_record_audit.json`): 64 source-record review rows, 87 boundary inputs, 4 conclusion dependencies, 1 recursive field, 0 source-record-only unresolved conclusion dependencies, 0 recursion failures.
- Review-surface audit (`audit/review_surface_llm.json`): review surface passed over 64 review rows.
- Holistic source-first audit (`docs/AGENT_SOURCE_AUDIT.md`): status not inferred by this generator.
- DAG/source/source-json audit (`docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`): status not inferred by this generator.
<!-- END GENERATED LLM-AS-JUDGE RESULTS -->


- `lake build DSWG24DiscretizationBias`: passes (2,604 jobs).
- Lean source: 27,227 lines, including the 1,330-line `PaperInterface.lean`.
- statement-match v10 and Lean-to-TeX v3: raw artifacts exist for the 55
  non-assumption rows, but exact semantic projection binds no current statement
  receipt on the 64-row surface.
- paper coverage v4 records dispositions for all 96 items; the source map still
  requires an explicit coverage-mode migration before closeout.
- assumption provenance v3: all nine raw receipts are diagnostic-only because
  none binds the current cached condition identity.
- review-surface v2: a structural 64-row receipt is recorded, but it does not
  establish current row-level semantic judgments.
- source-record v7: 80 current judgments plus 8 boundary inputs discharged by
  complete claim-bearing ledgers; zero unresolved conclusion dependencies.
- evidence-integrity source-obligation audit: zero errors; the only warning is
  the intentionally empty human review queue.
- `docs/DependencyDAG.pdf`: rebuilt and visually inspected.

The paper is not closed under the current exact-content protocol until the
coverage mode and statement/condition receipts are migrated. Separate human
review also remains incomplete.

## 18. Paper Definitions Checked

The checked definition surface includes the paper's classifiers, reference
rules, bias and fidelity quantities, Bayesian posteriors, iid data laws, and
dataset-dependent augmented reference family.

## 19. Named Theorem Statements Checked

Theorems 1 and 2, including the repaired clauses 1(ii) and 2(iii), have direct
source-shaped paper-facing statements. The Appendix B.1 support needed for
Theorem 2(iii) is formalized without turning proof support into an additional
named result.

## 20. Paper-Facing Statement Validator Ledger

The configured surface contains 64 rows: 55 statement rows and nine source
conditions. Exact semantic projection currently binds neither the raw
statement receipts nor the raw condition receipts, so both sets remain
diagnostic-only. Independent human review is `0/64`; no human sign-off is
claimed.

<!-- BEGIN GENERATED STATEMENT VALIDATOR LEDGER -->
### Current Canonical Evidence
Independent human dashboard review: 0/64 rows. No human row-level approval is inferred. review surface passed; Agent check by Codex DSWG24 paper-surface curator 2026-07-18; 2026-07-19 Diagnostic-only evidence excluded from this paper-facing ledger: 64 unconfigured, stale, or ambiguous statement-sidecar rows, 9 unconfigured, stale, or ambiguous source-condition sidecar rows.

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| - Prior class probability `Pr(y)`. | `prior` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DSWG24 context-free Lean translator 2026-07-18; 2026-07-18 | None recorded |
| Accuracy | `accuracy` | No completed statement check recorded. No Lean translation recorded | None recorded |
| - Marginal label share `\hat p_marg(y) = (1/N) sum_i 1[\hat y_i = y]`. | `marginalLabelShare` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DSWG24 context-free Lean translator 2026-07-18; 2026-07-18 | None recorded |
| - Aggregate posterior `p_agg^q(y) = (1/N) sum_i q(y,x_i)`. | `aggregatePosterior` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DSWG24 context-free Lean translator 2026-07-18; 2026-07-18 | None recorded |
| IsFirstArgmax formula | `isFirstArgmax_formula` | No completed statement check recorded. No Lean translation recorded | None recorded |
| IsTieBrokenArgmaxRule formula | `isTieBrokenArgmaxRule_formula` | No completed statement check recorded. No Lean translation recorded | None recorded |
| ThresholdRule | `thresholdRule` | No completed statement check recorded. No Lean translation recorded | None recorded |
| IsThompsonSamplingRule formula | `isThompsonSamplingRule_formula` | No completed statement check recorded. No Lean translation recorded | None recorded |
| IsIndependentRule formula | `isIndependentRule_formula` | No completed statement check recorded. No Lean translation recorded | None recorded |
| IsIndependentRandomizedRule formula | `isIndependentRandomizedRule_formula` | No completed statement check recorded. No Lean translation recorded | None recorded |
| - Bias `bias(y, \hat y, p_ref) = \hat p_marg(y) - p_ref(y)`. | `bias` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DSWG24 context-free Lean translator 2026-07-18; 2026-07-18 | None recorded |
| - Distributional fidelity `fid(p_ref, \hat y) = -sum_y \|bias(y,\hat y,p_ref)\|`. | `fidelity` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DSWG24 context-free Lean translator 2026-07-18; 2026-07-18 | None recorded |
| Equation1Objective | `equation1Objective` | No completed statement check recorded. No Lean translation recorded | None recorded |
| MaximizesEquation1 formula | `maximizesEquation1_formula` | No completed statement check recorded. No Lean translation recorded | None recorded |
| - Predictive MAE for Bayes posterior scores: `E_X sum_y q(y,x)(1-q(y,x))`. | `classifierMAE` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DSWG24 context-free Lean translator 2026-07-18; 2026-07-18 | None recorded |
| - Continuous marginal label share: `∫ x, 1[rule x = y] dμ(x)`. | `continuousMarginalLabelShare` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DSWG24 context-free Lean translator 2026-07-18; 2026-07-18 | None recorded |
| - Continuous aggregate posterior reference: `∫ x, q x y dμ(x)`. | `continuousAggregatePosterior` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DSWG24 context-free Lean translator 2026-07-18; 2026-07-18 | None recorded |
| - Continuous bias relative to a supplied reference distribution. | `continuousBias` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DSWG24 context-free Lean translator 2026-07-18; 2026-07-18 | None recorded |
| - Continuous aggregate-posterior bias. | `continuousAggregateBias` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DSWG24 context-free Lean translator 2026-07-18; 2026-07-18 | None recorded |
| - Continuous predictive MAE. | `continuousClassifierMAE` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DSWG24 context-free Lean translator 2026-07-18; 2026-07-18 | None recorded |
| - Joint prior-reference bias for Theorem 1's continuous statement. | `continuousJointPriorBias` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DSWG24 context-free Lean translator 2026-07-18; 2026-07-18 | None recorded |
| - Joint predictive MAE for Theorem 1's continuous statement. | `continuousJointClassifierMAE` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DSWG24 context-free Lean translator 2026-07-18; 2026-07-18 | None recorded |
| PosteriorSimplex formula | `posteriorSimplex_formula` | No completed statement check recorded. No Lean translation recorded | None recorded |
| IsArgmaxRule formula | `isArgmaxRule_formula` | No completed statement check recorded. No Lean translation recorded | None recorded |
| BayesOptimal formula | `bayesOptimal_formula` | No completed statement check recorded. No Lean translation recorded | None recorded |
| PerfectClassifierOnSupport formula | `perfectClassifierOnSupport_formula` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Calibrated formula | `calibrated_formula` | No completed statement check recorded. No Lean translation recorded | None recorded |
| - Paper objective `O_N^gamma` for one observed dataset: `γ` times average posterior score plus `(1 - γ)` times the fidelity term. | `objective` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DSWG24 context-free Lean translator 2026-07-18; 2026-07-18 | None recorded |
| - Expected paper objective using true-label accuracy plus expected fidelity. | `expectedObjective` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DSWG24 context-free Lean translator 2026-07-18; 2026-07-18 | None recorded |
| Equation2ExpectedAccuracy | `equation2ExpectedAccuracy` | No completed statement check recorded. No Lean translation recorded | None recorded |
| ExpectedFidelityAt | `expectedFidelityAt` | No completed statement check recorded. No Lean translation recorded | None recorded |
| ExpectedBiasAt | `expectedBiasAt` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Equation3ExpectedObjective | `equation3ExpectedObjective` | No completed statement check recorded. No Lean translation recorded | None recorded |
| ParetoOptimal formula | `paretoOptimal_formula` | No completed statement check recorded. No Lean translation recorded | None recorded |
| ReferenceSimplexAt formula | `referenceSimplexAt_formula` | No completed statement check recorded. No Lean translation recorded | None recorded |
| IsAggregateFirstArgmax formula | `isAggregateFirstArgmax_formula` | No completed statement check recorded. No Lean translation recorded | None recorded |
| SourcePNq formula | `sourcePNq_formula` | No completed statement check recorded. No Lean translation recorded | None recorded |
| SourceSa formula | `sourceSa_formula` | No completed statement check recorded. No Lean translation recorded | None recorded |
| SourceSb formula | `sourceSb_formula` | No completed statement check recorded. No Lean translation recorded | None recorded |
| SourceSc formula | `sourceSc_formula` | No completed statement check recorded. No Lean translation recorded | None recorded |
| SourceSd formula | `sourceSd_formula` | No completed statement check recorded. No Lean translation recorded | None recorded |
| SourceSe formula | `sourceSe_formula` | No completed statement check recorded. No Lean translation recorded | None recorded |
| states the no-information plurality-class and non-plurality-class bias formulas for both prior and aggregate-posterior references. | `theorem1i_no_information_bias` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DSWG24 context-free Lean translator 2026-07-18; 2026-07-18 | None recorded |
| Theorem1iiPriorReferenceZeroBiasSpec | `theorem1iiPriorReferenceZeroBiasSpec` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem1ii prior reference zero bias on support spec | `theorem1ii_prior_reference_zero_bias_on_support_spec` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem1iiAggregateReferenceZeroBiasSpec | `theorem1iiAggregateReferenceZeroBiasSpec` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem1ii aggregate reference zero bias on support spec | `theorem1ii_aggregate_reference_zero_bias_on_support_spec` | No completed statement check recorded. No Lean translation recorded | None recorded |
| states the calibrated argmax bias bound by predictive MAE. | `theorem1iii_argmax_bias_le_mae` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DSWG24 context-free Lean translator 2026-07-18; 2026-07-18 | None recorded |
| states the tight binary example where argmax bias equals MAE. | `theorem1iii_tight_binary_example` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DSWG24 context-free Lean translator 2026-07-18; 2026-07-18 | None recorded |
| states existence of a joint expected-objective maximizer. | `theorem2i_joint_rule_exists` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DSWG24 context-free Lean translator 2026-07-18; 2026-07-18 | None recorded |
| states argmax expected-accuracy optimality for Bayes-optimal scores. | `theorem2ii_argmax_accuracy_maximizing` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DSWG24 context-free Lean translator 2026-07-18; 2026-07-18 | None recorded |
| Theorem2iiiParetoOptimalAgreesArgmaxSpec | `theorem2iiiParetoOptimalAgreesArgmaxSpec` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem2iii source pareto optimal agrees argmax spec | `theorem2iii_source_pareto_optimal_agrees_argmax_spec` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem2iiiWeightedObjectiveMaximizerAgreesArgmaxSpec | `theorem2iiiWeightedObjectiveMaximizerAgreesArgmaxSpec` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem2iii source weighted objective maximizer agrees argmax spec | `theorem2iii_source_weighted_objective_maximizer_agrees_argmax_spec` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem 1. Argmax bias depends on predictive uncertainty, i.e., how much information features x provide about the true class label. Consider calibrated classifier q and the argmax decision rule Dargmax . Let N > K and consider a reference distribution of either the aggregate posterior or the prior. Then, (i). Suppose x provides no information and q(y, x) = Pr(y) for all x, y. Then, amplification bias is maximized... | `assumption_theorem1_no_information_case` | No completed source-condition check recorded | None recorded |
| Theorem 1. Argmax bias depends on predictive uncertainty, i.e., how much information features x provide about the true class label. Consider calibrated classifier q and the argmax decision rule Dargmax . Let N > K and consider a reference distribution of either the aggregate posterior or the prior. Then, (i). Suppose x provides no information and q(y, x) = Pr(y) for all x, y. Then, amplification bias is maximized... | `assumption_theorem1_plurality_argmax_class` | No completed source-condition check recorded | None recorded |
| Theorem 1. Argmax bias depends on predictive uncertainty, i.e., how much information features x provide about the true class label. Consider calibrated classifier q and the argmax decision rule Dargmax . Let N > K and consider a reference distribution of either the aggregate posterior or the prior. Then, (i). Suppose x provides no information and q(y, x) = Pr(y) for all x, y. Then, amplification bias is maximized... | `assumption_theorem1_perfect_classifier` | No completed source-condition check recorded | None recorded |
| Theorem 1. Argmax bias depends on predictive uncertainty, i.e., how much information features x provide about the true class label. Consider calibrated classifier q and the argmax decision rule Dargmax . Let N > K and consider a reference distribution of either the aggregate posterior or the prior. Then, (i). Suppose x provides no information and q(y, x) = Pr(y) for all x, y. Then, amplification bias is maximized... | `assumption_theorem1_argmax_rule_measurable` | No completed source-condition check recorded | None recorded |
| Theorem 1. Argmax bias depends on predictive uncertainty, i.e., how much information features x provide about the true class label. Consider calibrated classifier q and the argmax decision rule Dargmax . Let N > K and consider a reference distribution of either the aggregate posterior or the prior. Then, (i). Suppose x provides no information and q(y, x) = Pr(y) for all x, y. Then, amplification bias is maximized... | `assumption_theorem1_calibrated_classifier` | No completed source-condition check recorded | None recorded |
| Theorem 2. Consider Bayes optimal q, and N > K. For all F : (i). For every γ, pref there exists a joint decision-making rule that maximizes Oγ (D, q, pref ) in Equation (3). (ii). The argmax decision rule Dargmax maximizes O1 (D, q, pref ), i.e., is accuracy maximizing. (iii). Dargmax is the only Pareto optimal independent decision rule for non-trivial pref ∈ P. No independent decision rule D maximizes objective O... | `assumption_theorem2_at_least_two_classes` | No completed source-condition check recorded | None recorded |
| Theorem 2. Consider Bayes optimal q, and N > K. For all F : (i). For every γ, pref there exists a joint decision-making rule that maximizes Oγ (D, q, pref ) in Equation (3). (ii). The argmax decision rule Dargmax maximizes O1 (D, q, pref ), i.e., is accuracy maximizing. (iii). Dargmax is the only Pareto optimal independent decision rule for non-trivial pref ∈ P. No independent decision rule D maximizes objective O... | `assumption_theorem2_more_rows_than_classes` | No completed source-condition check recorded | None recorded |
| Theorem 2. Consider Bayes optimal q, and N > K. For all F : (i). For every γ, pref there exists a joint decision-making rule that maximizes Oγ (D, q, pref ) in Equation (3). (ii). The argmax decision rule Dargmax maximizes O1 (D, q, pref ), i.e., is accuracy maximizing. (iii). Dargmax is the only Pareto optimal independent decision rule for non-trivial pref ∈ P. No independent decision rule D maximizes objective O... | `assumption_theorem2_positive_sample_count` | No completed source-condition check recorded | None recorded |
| Theorem 2. Consider Bayes optimal q, and N > K. For all F : (i). For every γ, pref there exists a joint decision-making rule that maximizes Oγ (D, q, pref ) in Equation (3). (ii). The argmax decision rule Dargmax maximizes O1 (D, q, pref ), i.e., is accuracy maximizing. (iii). Dargmax is the only Pareto optimal independent decision rule for non-trivial pref ∈ P. No independent decision rule D maximizes objective O... | `assumption_theorem2_reference_nonnegative` | No completed source-condition check recorded | None recorded |
<!-- END GENERATED STATEMENT VALIDATOR LEDGER -->

## 21. Source-Coverage Audit Ledger

- Source inventory: 96 items from the pinned 2,379-line audit source.
- Coverage result: 62 covered items, 18 support-only items, and 16 recorded
  scope exclusions.
- Scope migration: the source map has no explicit coverage mode, so the
  canonical ledger conservatively renders the full inventory until that field
  is migrated.
- Row-local statement checks: none of the 62 linked references has an exact
  current semantic receipt; the raw receipts remain diagnostic-only.

<!-- BEGIN GENERATED SOURCE COVERAGE LEDGER -->
### Current Canonical Evidence
- Coverage scope: full inventory shown because scope metadata needs repair (paper_statement_map.json must explicitly set source_coverage_mode before a source-coverage closeout).
- Source inventory: 96 source statements from `.audit_source/DSWG24DiscretizationBias.txt`.
- Coverage result: 62 covered, 16 out of scope, 18 support only.
- Coverage review: coverage ledger recorded; Agent check by Codex DSWG24 source inventory coverage auditor 2026-07-18; 2026-07-19.
- Row-local statement checks: 0/62 linked row references have a completed canonical statement check; repeated links are counted per source row.

| Source statement | Linked Lean review rows | Coverage judgment | Row-local statement checks | Comments |
| --- | --- | --- | --- | --- |
| On the source proof's selected dataset, P_N^q's one-label lower bound suffices for a one-row switch that weakly improves accuracy and strictly improves fidelity. | None recorded | support only | No linked paper-facing row recorded | This inventory item is a proof-region definition, intermediate equation, or local bridge used to audit the paper proof. It supports the listed reviewed or auxiliary Lean declarations but is not a standalone paper theorem target. |
| For gamma below one, the same selected-dataset switch strictly improves the weighted accuracy/fidelity objective. | None recorded | support only | No linked paper-facing row recorded | This inventory item is a proof-region definition, intermediate equation, or local bridge used to audit the paper proof. It supports the listed reviewed or auxiliary Lean declarations but is not a standalone paper theorem target. |
| In Theorem 1(i), the plurality argmax class has bias `1-Pr(y)` in the no-information regime. | `theorem1i_no_information_bias` | covered | `theorem1i_no_information_bias`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| In Theorem 1(i), every non-plurality class has bias `-Pr(y)` in the no-information regime. | `theorem1i_no_information_bias` | covered | `theorem1i_no_information_bias`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| Theorem 1(ii) gives zero expected bias for a perfect classifier when the reference is the prior. | `theorem1ii_prior_reference_zero_bias_on_support_spec` | covered | `theorem1ii_prior_reference_zero_bias_on_support_spec`: no completed statement check | The reviewed theorem proves the exact support-sensitive perfect-classifier implication for every label with the prior reference, using positive joint support rather than a stronger global score premise. |
| Theorem 1(ii) gives zero expected bias for a perfect classifier when the reference is the aggregate posterior. | `theorem1ii_aggregate_reference_zero_bias_on_support_spec` | covered | `theorem1ii_aggregate_reference_zero_bias_on_support_spec`: no completed statement check | The reviewed theorem proves the exact support-sensitive perfect-classifier implication for every label with the aggregate-posterior reference and derives the reference identity from positive joint support. |
| Equation (4): calibrated argmax class bias is bounded above by classifier MAE. | None recorded | support only | No linked paper-facing row recorded | This inventory item is a proof-region definition, intermediate equation, or local bridge used to audit the paper proof. It supports the listed reviewed or auxiliary Lean declarations but is not a standalone paper theorem target. |
| Equation (5): decompose the plurality-class prior mass over S_a, S_c, and S_e. | None recorded | out of scope | No linked paper-facing row recorded | This source item is an intermediate displayed proof equation with no standalone theorem claim; it remains pinned in the source inventory for proof traceability and does not require its own dashboard theorem row. |
| Equation (6): the plurality-class prior equals `a + c/K` in the reduced worst-case shape. | None recorded | out of scope | No linked paper-facing row recorded | This source item is an intermediate displayed proof equation with no standalone theorem claim; it remains pinned in the source inventory for proof traceability and does not require its own dashboard theorem row. |
| Equation (7): calibration at posterior score delta identifies the conditional true-label probability with delta. | None recorded | support only | No linked paper-facing row recorded | This inventory item is a proof-region definition, intermediate equation, or local bridge used to audit the paper proof. It supports the listed reviewed or auxiliary Lean declarations but is not a standalone paper theorem target. |
| Equation (8): classifier MAE as the joint integral of absolute posterior error at the realized label. | None recorded | support only | No linked paper-facing row recorded | This inventory item is a proof-region definition, intermediate equation, or local bridge used to audit the paper proof. It supports the listed reviewed or auxiliary Lean declarations but is not a standalone paper theorem target. |
| Equation (9): split MAE into the focal-label and nonfocal-label contributions. | None recorded | out of scope | No linked paper-facing row recorded | This source item is an intermediate displayed proof equation with no standalone theorem claim; it remains pinned in the source inventory for proof traceability and does not require its own dashboard theorem row. |
| Equation (10): evaluate the S_a contribution using the reduced region definitions. | None recorded | support only | No linked paper-facing row recorded | This inventory item is a proof-region definition, intermediate equation, or local bridge used to audit the paper proof. It supports the listed reviewed or auxiliary Lean declarations but is not a standalone paper theorem target. |
| Equation (11): evaluate the S_e contribution under a perfect nonfocal class. | None recorded | support only | No linked paper-facing row recorded | This inventory item is a proof-region definition, intermediate equation, or local bridge used to audit the paper proof. It supports the listed reviewed or auxiliary Lean declarations but is not a standalone paper theorem target. |
| Equation (12): collect the S_c contribution to MAE. | None recorded | support only | No linked paper-facing row recorded | This inventory item is a proof-region definition, intermediate equation, or local bridge used to audit the paper proof. It supports the listed reviewed or auxiliary Lean declarations but is not a standalone paper theorem target. |
| Equation (13): use calibration implications to reduce MAE to the middle-region mass term. | None recorded | support only | No linked paper-facing row recorded | This inventory item is a proof-region definition, intermediate equation, or local bridge used to audit the paper proof. It supports the listed reviewed or auxiliary Lean declarations but is not a standalone paper theorem target. |
| Equation (14): the argmax marginal share of the plurality class is `a+c`. | None recorded | out of scope | No linked paper-facing row recorded | This source item is an intermediate displayed proof equation with no standalone theorem claim; it remains pinned in the source inventory for proof traceability and does not require its own dashboard theorem row. |
| Equation (15): target aggregate-posterior preservation for the S_b transformation. | None recorded | out of scope | No linked paper-facing row recorded | This source item is an intermediate displayed proof equation with no standalone theorem claim; it remains pinned in the source inventory for proof traceability and does not require its own dashboard theorem row. |
| Equation (16): rewrite S_b aggregate preservation as equality of the changed-region integrals. | None recorded | out of scope | No linked paper-facing row recorded | This source item is an intermediate displayed proof equation with no standalone theorem claim; it remains pinned in the source inventory for proof traceability and does not require its own dashboard theorem row. |
| Equation (17): balance the lower and upper S_b score-mass changes. | None recorded | out of scope | No linked paper-facing row recorded | This source item is an intermediate displayed proof equation with no standalone theorem claim; it remains pinned in the source inventory for proof traceability and does not require its own dashboard theorem row. |
| Equation (18): express the MAE change for the first source transformation. | None recorded | out of scope | No linked paper-facing row recorded | This source item is an intermediate displayed proof equation with no standalone theorem claim; it remains pinned in the source inventory for proof traceability and does not require its own dashboard theorem row. |
| Equation (19): split the first transformation's MAE change by changed regions and labels. | None recorded | out of scope | No linked paper-facing row recorded | This source item is an intermediate displayed proof equation with no standalone theorem claim; it remains pinned in the source inventory for proof traceability and does not require its own dashboard theorem row. |
| Equation (20): reduce the first transformation's MAE delta to the balanced score-mass terms. | None recorded | out of scope | No linked paper-facing row recorded | This source item is an intermediate displayed proof equation with no standalone theorem claim; it remains pinned in the source inventory for proof traceability and does not require its own dashboard theorem row. |
| Equation (21): the balanced first transformation preserves MAE. | None recorded | out of scope | No linked paper-facing row recorded | This source item is an intermediate displayed proof equation with no standalone theorem claim; it remains pinned in the source inventory for proof traceability and does not require its own dashboard theorem row. |
| Equation (22): express the MAE change for the second source transformation. | None recorded | out of scope | No linked paper-facing row recorded | This source item is an intermediate displayed proof equation with no standalone theorem claim; it remains pinned in the source inventory for proof traceability and does not require its own dashboard theorem row. |
| Equation (23): split the second transformation's MAE change by changed regions and labels. | None recorded | out of scope | No linked paper-facing row recorded | This source item is an intermediate displayed proof equation with no standalone theorem claim; it remains pinned in the source inventory for proof traceability and does not require its own dashboard theorem row. |
| Equation (24): reduce the second transformation's MAE delta to balanced score-mass terms. | None recorded | out of scope | No linked paper-facing row recorded | This source item is an intermediate displayed proof equation with no standalone theorem claim; it remains pinned in the source inventory for proof traceability and does not require its own dashboard theorem row. |
| Equation (25): the balanced second transformation preserves MAE. | None recorded | out of scope | No linked paper-facing row recorded | This source item is an intermediate displayed proof equation with no standalone theorem claim; it remains pinned in the source inventory for proof traceability and does not require its own dashboard theorem row. |
| Equation (26): at gamma=1 the weighted objective is expected accuracy. | None recorded | support only | No linked paper-facing row recorded | This inventory item is a proof-region definition, intermediate equation, or local bridge used to audit the paper proof. It supports the listed reviewed or auxiliary Lean declarations but is not a standalone paper theorem target. |
| Equation (27): expand expected accuracy as expectation of finite-sample accuracy. | None recorded | support only | No linked paper-facing row recorded | This inventory item is a proof-region definition, intermediate equation, or local bridge used to audit the paper proof. It supports the listed reviewed or auxiliary Lean declarations but is not a standalone paper theorem target. |
| Equation (28): expand finite-sample accuracy into averaged correctness indicators. | None recorded | support only | No linked paper-facing row recorded | This inventory item is a proof-region definition, intermediate equation, or local bridge used to audit the paper proof. It supports the listed reviewed or auxiliary Lean declarations but is not a standalone paper theorem target. |
| Equation (29): apply the tower property conditional on the observed feature dataset. | None recorded | out of scope | No linked paper-facing row recorded | This source item is an intermediate displayed proof equation with no standalone theorem claim; it remains pinned in the source inventory for proof traceability and does not require its own dashboard theorem row. |
| Equation (30): use independent sampling to separate row-wise conditional expectations. | None recorded | support only | No linked paper-facing row recorded | This inventory item is a proof-region definition, intermediate equation, or local bridge used to audit the paper proof. It supports the listed reviewed or auxiliary Lean declarations but is not a standalone paper theorem target. |
| Equation (31): replace each conditional correctness probability by the Bayes posterior score. | None recorded | support only | No linked paper-facing row recorded | This inventory item is a proof-region definition, intermediate equation, or local bridge used to audit the paper proof. It supports the listed reviewed or auxiliary Lean declarations but is not a standalone paper theorem target. |
| Equation (32): row-wise posterior scores are weakly increased by the tie-broken argmax choice. | None recorded | support only | No linked paper-facing row recorded | This inventory item is a proof-region definition, intermediate equation, or local bridge used to audit the paper proof. It supports the listed reviewed or auxiliary Lean declarations but is not a standalone paper theorem target. |
| Equation (33): identify the resulting upper bound with the argmax rule's gamma=1 objective. | None recorded | support only | No linked paper-facing row recorded | This inventory item is a proof-region definition, intermediate equation, or local bridge used to audit the paper proof. It supports the listed reviewed or auxiliary Lean declarations but is not a standalone paper theorem target. |
| Support specialization: zero prior-reference bias under the stronger premise that the decision agrees with truth on every product pair. | None recorded | support only | No linked paper-facing row recorded | This inventory item is a proof-region definition, intermediate equation, or local bridge used to audit the paper proof. It supports the listed reviewed or auxiliary Lean declarations but is not a standalone paper theorem target. |
| For the exact dataset-dependent P_N^q reference family, argmax is the only Pareto-optimal independent rule; a positively disagreeing independent rule is not Pareto optimal. | `theorem2iii_source_pareto_optimal_agrees_argmax_spec` | covered | `theorem2iii_source_pareto_optimal_agrees_argmax_spec`: no completed statement check | The reviewed theorem lifts the source's one-dataset switch through a positive-mass iid sample event while evaluating fidelity at the exact dataset-indexed P_N^q reference, proving Pareto optimality implies almost-sure argmax agreement. |
| For the exact dataset-dependent P_N^q reference family and 0 <= gamma < 1, every independent rule that maximizes O_N^gamma agrees with argmax almost surely. | `theorem2iii_source_weighted_objective_maximizer_agrees_argmax_spec` | covered | `theorem2iii_source_weighted_objective_maximizer_agrees_argmax_spec`: no completed statement check | The reviewed theorem proves the Appendix-supported weighted necessity clause for 0 <= gamma < 1: an independent expected-objective maximizer under the exact dataset-dependent P_N^q reference must agree with argmax almost surely. It does not claim the main text's overbroad converse that gamma=1 is necessary for an already agreeing rule. |
| states the accuracy-boundary strict-disagreement non-maximality claim. | None recorded | support only | No linked paper-facing row recorded | This inventory item is a proof-region definition, intermediate equation, or local bridge used to audit the paper proof. It supports the listed reviewed or auxiliary Lean declarations but is not a standalone paper theorem target. |
| Finite observed-label accuracy is `acc(y_1:N, yhat_1:N) = (1/N) sum_i 1[yhat_i = y_i]`. | `accuracy` | covered | `accuracy`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| The source uses one fixed consistent ordering to choose the first class among tied posterior-score maximizers. | `isFirstArgmax_formula` | covered | `isFirstArgmax_formula`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| The argmax rule assigns each row its posterior-maximizing class using the source's fixed tie order. | `isTieBrokenArgmaxRule_formula` | covered | `isTieBrokenArgmaxRule_formula`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| Threshold-at-t emits the tie-broken argmax label when its maximum posterior score is at least t and otherwise leaves the row uncoded. | `thresholdRule` | covered | `thresholdRule`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| Under Thompson sampling, row i receives class y with probability q(y,x_i). | `isThompsonSamplingRule_formula` | covered | `isThompsonSamplingRule_formula`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| For a deterministic independent rule, the decision at row i is one common function d of q(x_i), independent of the other dataset rows. | `isIndependentRule_formula` | covered | `isIndependentRule_formula`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| For a randomized independent rule, conditional decision-vector probabilities factor into row-level probabilities depending only on each row. | `isIndependentRandomizedRule_formula` | covered | `isIndependentRandomizedRule_formula`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| Equation (1) scores a decision vector by gamma times average posterior score plus (1-gamma) times fidelity to the supplied reference. | `equation1Objective` | covered | `equation1Objective`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| The Equation (1) joint rule returns a decision vector maximizing the per-dataset weighted score over all label assignments. | `maximizesEquation1_formula` | covered | `maximizesEquation1_formula`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| The Bayes-optimal posterior satisfies `q*(y,x) = Pr(Y=y \| X=x)`; the finite interface uses the equivalent atom factorization on nonzero and zero observation atoms. | `bayesOptimal_formula` | covered | `bayesOptimal_formula`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| Theorem 1(ii)'s perfect classifier is one-hot at the realized true class under the joint data law. | `perfectClassifierOnSupport_formula` | covered | `perfectClassifierOnSupport_formula`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| Equation (2) defines ACC_N(D,q) as expected finite-sample 0-1 accuracy over sampled datasets and rule randomness. | `equation2ExpectedAccuracy` | covered | `equation2ExpectedAccuracy`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| FID_N(D,q,pref) is expected per-dataset fidelity, with the reference allowed to depend on the observed dataset. | `expectedFidelityAt` | covered | `expectedFidelityAt`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| BIAS_N(y,D,q,pref) is expected per-dataset class bias under the sampled-data law and rule randomness. | `expectedBiasAt` | covered | `expectedBiasAt`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| Equation (3) is `O_N^gamma = gamma ACC_N + (1-gamma) FID_N`. | `equation3ExpectedObjective` | covered | `equation3ExpectedObjective`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| A decision rule is Pareto optimal for expected accuracy and expected fidelity; equivalently in the paper, it maximizes the weighted objective for some gamma in (0,1]. | `paretoOptimal_formula` | covered | `paretoOptimal_formula`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| A source reference family maps each observed dataset to a probability distribution on labels. | `referenceSimplexAt_formula` | covered | `referenceSimplexAt_formula`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| For one dataset, the selected reference-constrained label is the tie-broken class maximizing the aggregate posterior score sum over rows. | `isAggregateFirstArgmax_formula` | covered | `isAggregateFirstArgmax_formula`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| The exact P_N^q family is dataset-indexed and simplex-valued, and requires mass at least 1/N only at that dataset's selected aggregate-max class. | `sourcePNq_formula` | covered | `sourcePNq_formula`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| - Prior class probability `Pr(y)`. | `prior` | covered | `prior`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| - Marginal label share `\hat p_marg(y) = (1/N) sum_i 1[\hat y_i = y]`. | `marginalLabelShare` | covered | `marginalLabelShare`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| - Aggregate posterior `p_agg^q(y) = (1/N) sum_i q(y,x_i)`. | `aggregatePosterior` | covered | `aggregatePosterior`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| - Bias `bias(y, \hat y, p_ref) = \hat p_marg(y) - p_ref(y)`. | `bias` | covered | `bias`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| - Distributional fidelity `fid(p_ref, \hat y) = -sum_y \|bias(y,\hat y,p_ref)\|`. | `fidelity` | covered | `fidelity`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| - Predictive MAE for Bayes posterior scores: `E_X sum_y q(y,x)(1-q(y,x))`. | `classifierMAE` | covered | `classifierMAE`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| - Continuous marginal label share: `∫ x, 1[rule x = y] dμ(x)`. | `continuousMarginalLabelShare` | covered | `continuousMarginalLabelShare`: no completed statement check | This source-visible proof definition, formula, or named theorem endpoint is exposed by exactly one reviewed row with a current v10 semantic ledger; its proof-support inventory role does not reduce the coverage of that source-facing row. |
| - Continuous aggregate posterior reference: `∫ x, q x y dμ(x)`. | `continuousAggregatePosterior` | covered | `continuousAggregatePosterior`: no completed statement check | This source-visible proof definition, formula, or named theorem endpoint is exposed by exactly one reviewed row with a current v10 semantic ledger; its proof-support inventory role does not reduce the coverage of that source-facing row. |
| - Continuous bias relative to a supplied reference distribution. | `continuousBias` | covered | `continuousBias`: no completed statement check | This source-visible proof definition, formula, or named theorem endpoint is exposed by exactly one reviewed row with a current v10 semantic ledger; its proof-support inventory role does not reduce the coverage of that source-facing row. |
| - Continuous aggregate-posterior bias. | `continuousAggregateBias` | covered | `continuousAggregateBias`: no completed statement check | This source-visible proof definition, formula, or named theorem endpoint is exposed by exactly one reviewed row with a current v10 semantic ledger; its proof-support inventory role does not reduce the coverage of that source-facing row. |
| - Continuous predictive MAE. | `continuousClassifierMAE` | covered | `continuousClassifierMAE`: no completed statement check | This source-visible proof definition, formula, or named theorem endpoint is exposed by exactly one reviewed row with a current v10 semantic ledger; its proof-support inventory role does not reduce the coverage of that source-facing row. |
| - Joint prior-reference bias for Theorem 1's continuous statement. | `continuousJointPriorBias` | covered | `continuousJointPriorBias`: no completed statement check | This source-visible proof definition, formula, or named theorem endpoint is exposed by exactly one reviewed row with a current v10 semantic ledger; its proof-support inventory role does not reduce the coverage of that source-facing row. |
| - Joint predictive MAE for Theorem 1's continuous statement. | `continuousJointClassifierMAE` | covered | `continuousJointClassifierMAE`: no completed statement check | This source-visible proof definition, formula, or named theorem endpoint is exposed by exactly one reviewed row with a current v10 semantic ledger; its proof-support inventory role does not reduce the coverage of that source-facing row. |
| - Posterior-simplex condition: each `q(x)` is a probability vector. | `posteriorSimplex_formula` | covered | `posteriorSimplex_formula`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| - Tie-broken argmax rule: the selected label has maximal posterior score. | `isArgmaxRule_formula` | covered | `isArgmaxRule_formula`: no completed statement check | This source-visible proof definition, formula, or named theorem endpoint is exposed by exactly one reviewed row with a current v10 semantic ledger; its proof-support inventory role does not reduce the coverage of that source-facing row. |
| - Calibration: for every label and every measurable score event, the true label mass on that score event equals the aggregate posterior score mass on the same event. This is the paper's `Pr(Y=y \| q(y,x)=c)=c` condition in event-preimage form. | `calibrated_formula` | covered | `calibrated_formula`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| - Paper objective `O_N^gamma` for one observed dataset: `γ` times average posterior score plus `(1 - γ)` times the fidelity term. | `objective` | covered | `objective`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| - Expected paper objective using true-label accuracy plus expected fidelity. | `expectedObjective` | covered | `expectedObjective`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| - Source proof region `S_a`: focal posterior is `1`. | `sourceSa_formula` | covered | `sourceSa_formula`: no completed statement check | This source-visible proof definition, formula, or named theorem endpoint is exposed by exactly one reviewed row with a current v10 semantic ledger; its proof-support inventory role does not reduce the coverage of that source-facing row. |
| - Source proof region `S_b`: focal posterior is in `(1/K,1)`. | `sourceSb_formula` | covered | `sourceSb_formula`: no completed statement check | This source-visible proof definition, formula, or named theorem endpoint is exposed by exactly one reviewed row with a current v10 semantic ledger; its proof-support inventory role does not reduce the coverage of that source-facing row. |
| - Source proof region `S_c`: focal posterior is exactly `1/K`. | `sourceSc_formula` | covered | `sourceSc_formula`: no completed statement check | This source-visible proof definition, formula, or named theorem endpoint is exposed by exactly one reviewed row with a current v10 semantic ledger; its proof-support inventory role does not reduce the coverage of that source-facing row. |
| - Source proof region `S_d`: focal posterior is in `(0,1/K)`. | `sourceSd_formula` | covered | `sourceSd_formula`: no completed statement check | This source-visible proof definition, formula, or named theorem endpoint is exposed by exactly one reviewed row with a current v10 semantic ledger; its proof-support inventory role does not reduce the coverage of that source-facing row. |
| - Source proof region `S_e`: focal posterior is `0`. | `sourceSe_formula` | covered | `sourceSe_formula`: no completed statement check | This source-visible proof definition, formula, or named theorem endpoint is exposed by exactly one reviewed row with a current v10 semantic ledger; its proof-support inventory role does not reduce the coverage of that source-facing row. |
| states the no-information plurality-class and non-plurality-class bias formulas for both prior and aggregate-posterior references. | `theorem1i_no_information_bias` | covered | `theorem1i_no_information_bias`: no completed statement check | This source-visible proof definition, formula, or named theorem endpoint is exposed by exactly one reviewed row with a current v10 semantic ledger; its proof-support inventory role does not reduce the coverage of that source-facing row. |
| states the calibrated argmax bias bound by predictive MAE. | `theorem1iii_argmax_bias_le_mae` | covered | `theorem1iii_argmax_bias_le_mae`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| states the tight binary example where argmax bias equals MAE. | `theorem1iii_tight_binary_example` | covered | `theorem1iii_tight_binary_example`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| states existence of a joint expected-objective maximizer. | `theorem2i_joint_rule_exists` | covered | `theorem2i_joint_rule_exists`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| states argmax expected-accuracy optimality for Bayes-optimal scores. | `theorem2ii_argmax_accuracy_maximizing` | covered | `theorem2ii_argmax_accuracy_maximizing`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| - Theorem 1(i) no-information regime. | `assumption_theorem1_no_information_case` | covered | `assumption_theorem1_no_information_case`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| - Theorem 1(i) fixes a plurality/argmax class for the no-information regime. | `assumption_theorem1_plurality_argmax_class` | covered | `assumption_theorem1_plurality_argmax_class`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| - Theorem 1(ii) perfect-classifier regime. | `assumption_theorem1_perfect_classifier` | covered | `assumption_theorem1_perfect_classifier`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| - The continuous Theorem 1(iii) wrapper requires a measurable argmax rule. | `assumption_theorem1_argmax_rule_measurable` | covered | `assumption_theorem1_argmax_rule_measurable`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| - Theorem 1 is stated for calibrated classifiers. | `assumption_theorem1_calibrated_classifier` | covered | `assumption_theorem1_calibrated_classifier`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| - Theorem 2 assumes at least two classes in the finite Lean wrapper. | `assumption_theorem2_at_least_two_classes` | covered | `assumption_theorem2_at_least_two_classes`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| - Theorem 2 states the sample-size condition `N > K`. | `assumption_theorem2_more_rows_than_classes` | covered | `assumption_theorem2_more_rows_than_classes`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| - Positive sample size is the formal consequence of the source `N > K` condition. | `assumption_theorem2_positive_sample_count` | covered | `assumption_theorem2_positive_sample_count`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
| - Non-trivial reference distributions are probability distributions. | `assumption_theorem2_reference_nonnegative` | covered | `assumption_theorem2_reference_nonnegative`: no completed statement check | The complete source definition, formula, premise, or theorem endpoint is exposed by the routed reviewed row; claim-bearing items are theorem-proved and the row has a complete current v10 semantic ledger. |
<!-- END GENERATED SOURCE COVERAGE LEDGER -->
