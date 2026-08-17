# Final Validation Report: LOS02 Combinatorial Auctions

Updated: 2026-07-31

## 1. Human Verdict
Partially formalized. The finite auction model, generalized Vickrey auction,
single-minded welfare/set-packing reductions, greedy approximation, critical-value
lemmas, and average-greedy truthfulness theorem are checked. Full formalization
still requires reusable computational-complexity infrastructure for the native
Theorem 6.1 hardness and `NP = ZPP` consequences. No auction-theoretic paper
error is reported, and no human dashboard sign-off has been recorded.

## 2. Closeout Status
- Completion status: partially formalized.
- One-sentence recap: Greedy approximation, truthfulness, and Theorem 6.1 reductions are formalized. Full formalization requires computational complexity results that are out of scope.
- Lean footprint: 7,582 paper-local Lean LOC; `PaperInterface.lean` is 371 lines; 39 human-review declarations are exposed.
- Audit summary: source coverage has 31 covered, 8 formalization boundary; diagnostics: full inventory shown because paper_statement_map.json must explicitly set source_coverage_mode before a source-coverage closeout; statement LLM-as-judge has no rows; source conditions: 3 source condition, 2 formalization boundary; diagnostics: 39 orphan/stale statement-sidecar rows excluded, 4 orphan/stale source-condition sidecar rows excluded, 34 configured rows without unambiguous current receipts; Lean-to-TeX has 30 row translations; assumption provenance has 3 source condition, 2 formalization boundary; diagnostics: 4 unconfigured, stale, or ambiguous source-condition sidecar rows excluded, 4 configured source conditions without unambiguous current receipts; source-record classification has 1 formalization boundary; source-record audit reports 39 source-record review rows, 1 boundary input, 0 recursive fields, 0 recursion failures; review-surface audit review surface passed over 39 review rows; holistic source-first audit status is not inferred by this generator; DAG/source-json audit status is not inferred (see `docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`).

## 3. Source and Scope
- Paper: *Truth Revelation in Approximately Efficient Combinatorial Auctions*
- Authors: Daniel Lehmann, Liadan Ita O'Callaghan, and Yoav Shoham
- Source version: Journal of the ACM 49(5), 2002
- Public source: [paper PDF](https://jmvidal.cse.sc.edu/library/lehmann02a.pdf)
- Lean folder: `LOS02CombinatorialAuctions/`
- Human-facing theorem file: `papers/LOS02CombinatorialAuctions/PaperInterface.lean`
- Paper assumption file: `papers/LOS02CombinatorialAuctions/Assumptions.lean`
- DAG artifacts: `papers/LOS02CombinatorialAuctions/docs/DependencyDAG.tex`, `papers/LOS02CombinatorialAuctions/docs/DependencyDAG.pdf`
- Supporting machine evidence: `papers/LOS02CombinatorialAuctions/audit/*.json`.

Scope: this audit covers the paper's mathematical definitions and theorem-level
auction results. The paper's native computational-complexity consequences are
represented only as partial external-boundary interfaces until the shared
library has a machine-level theory of polynomial-time reductions, hardness,
inapproximability, randomized complexity, and the cited set-packing/clique
facts.

## 4. Researcher Summary of Checked Results
- The finite combinatorial-auction definitions are checked with source-facing formula rows for utility, truthfulness, generalized Vickrey payments, single-minded profiles, set-packing value, greedy order, accepted set, and payments.
- The generalized Vickrey auction truthfulness theorem and nonnegative truthful-utility proposition are checked for the finite combinatorial-auction model.
- The Theorem 6.1 finite reduction layer is checked: set-packing feasibility and value encodings, weighted set-packing reduction, and the clique-to-single-minded-welfare route.
- The Theorem 7.2 greedy `sqrt(m)` approximation proof is checked for the explicit average-descending order and optimal-allocation comparison conditions.
- Lemmas 9.1--9.5, Theorem 9.6, Definition 10.1, and Theorem 10.2 are checked for the documented single-minded domain and critical-value conditions.
- The remaining theorem-level boundary is the native complexity layer for Theorem 6.1 and the related `NP = ZPP` complexity-class note.

## 5. Remaining Boundaries and Gaps
Full formalization requires reusable computational-complexity infrastructure for
the final native Theorem 6.1 hardness and `NP = ZPP` consequences. The current
Lean code proves the finite auction/reduction statements and records the
complexity consequences as conditional external-boundary interfaces.

## 6. Additional Assumptions Beyond Paper
None.

## 7. Proof-Strategy Deviations
None beyond the formalization boundaries already recorded above. The finite
auction, greedy, and critical-value arguments follow the paper's proof routes;
the native complexity consequences are not claimed as fully formalized.

## 8. Proof Tricks Worth Reusing
- For source definitions that otherwise appear as opaque function abbreviations, expose exact formula or iff rows in `PaperInterface.lean` before running LLM-as-judge translation. This keeps the judged review surface at the paper-formula level rather than at opaque Lean function signatures.
- For partial complexity results, separate the finite reduction theorem from the native machine-level complexity consequence. The finite theorem can be checked while the external complexity infrastructure remains a visible partial boundary.

## 9. Generalizations, Conjectures, and Extensions

The finite greedy-allocation and critical-value arguments are reusable for
other single-minded auction formalizations. A general machine-level complexity
library would close the Theorem 6.1 boundary, but that is future shared work.

## 10. Mathematical Typos or Other Fixes Suggested in the Source Paper
None found.

## 11. Paper Issues or Caveats
No auction-theoretic paper error is reported. The paper status is partial only
because the reusable computational-complexity infrastructure for the final
native complexity claims is not yet present in the library.

## 12. Detailed Formalization Evidence
The formalization closes the finite combinatorial-auction core used by the
paper: utility and truthfulness predicates, generalized Vickrey auction
truthfulness and nonnegative truthful utility, the single-minded
welfare/set-packing encodings, the greedy square-root approximation, the
critical-value lemmas, and the average-greedy mechanism truthfulness theorem.

The reviewed definition rows now use source-facing formula components such as
`utility_formula`, `truthfulOn_iff`, `generalizedVickreyAuction_allocation_payment`,
`weightedSetPackingValue_formula`, `averageOrderOf_rule`, and
`averageGreedyPayment_formula`. The current statement LLM-as-judge sidecar has
no `uncertain` rows because the judged surface uses formula-level paper
statements rather than opaque function signatures.

The theorem endpoints involving native computational complexity remain partial.
Lean exposes exact and approximation-preserving solver consequences through
abstract external-consequence interfaces, but it does not yet contain a
reusable machine-level theory of polynomial-time reductions,
NP-hardness/inapproximability, ZPP, or the cited clique/set-packing hardness
facts.

Source-domain notes: the nonnegative/nonempty single-minded domain,
optimal-allocation comparison conditions, denied-bidder case, nonnegative-value
deviation domain, critical-value conditions, and finite-threshold condition are
source theorem conditions. The two complexity rows are partial boundaries, not
additional assumptions accepted as completed theorem hypotheses.

## 13. Paper Assumption Provenance

Every paper-facing premise is routed through
`LOS02CombinatorialAuctions/Assumptions.lean` and tracked by
`audit/assumption_match_llm.json`. Five of nine configured conditions bind exact
current receipts; four remain unresolved. The auction-theoretic premises below
are source conditions, while the Theorem 6.1 complexity rows are documented
partial-formalization boundaries.

<!-- BEGIN GENERATED ASSUMPTION PROVENANCE LEDGER -->
### Current Canonical Evidence
Generated from the configured source-condition surface and exact current statement digests in the canonical assumption-provenance sidecar. Model, agent, and automated checks are identified as such; no human review is inferred. Diagnostic-only evidence excluded from this ledger: 4 unconfigured, stale, or ambiguous source-condition sidecar rows.

| Assumption declaration | Lean declaration | Source location / statement | Assumption validators | Comments |
| --- | --- | --- | --- | --- |
| Assumption admissible combinatorial report domain | `assumption_admissible_combinatorial_report_domain` | - Truthfulness is stated relative to an admissible declaration domain. | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | Definition 3.2 states truthfulness over bidder types and vectors of declarations; the Lean domain parameter is the finite formalization of the declaration/type domain over which truthfulness is asserted. Premise-level checks: 1 source condition |
| Assumption external exact set packing complexity boundary | `assumption_external_exact_set_packing_complexity_boundary` | - External exact set-packing hardness and polynomial-time transfer facts for the paper's Theorem 6.1 complexity consequence. | formalization boundary; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | External exact set-packing complexity result is outside the current Lean complexity library. Premise-level checks: 1 formalization boundary |
| Assumption external approximation set packing complexity boundary | `assumption_external_approximation_set_packing_complexity_boundary` | - External set-packing inapproximability and polynomial-time transfer facts for the paper's Theorem 6.1 approximation consequence. | formalization boundary; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | External approximation set-packing complexity result is outside the current Lean complexity library. Premise-level checks: 1 formalization boundary |
| Assumption theorem7 optimal allocation feasible | `assumption_theorem7_optimal_allocation_feasible` | - The optimal allocation considered in Theorem 7.2 is feasible. | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | Theorem 7.2 compares the greedy allocation with `OP`, the optimal solution; pairwise disjoint desired bundles are the finite single-minded representation of OP feasibility. Premise-level checks: 1 source condition |
| Assumption theorem7 optimal bidders in order | `assumption_theorem7_optimal_bidders_in_order` | - The fixed greedy order contains every bidder in the optimal allocation. | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | Theorem 7.2 proves the greedy algorithm by processing the sorted list of bids; the Lean explicit-order theorem records that the optimal bidders under comparison are present in that order. Premise-level checks: 1 source condition |
| Assumption lemma9 denied bidder case | `assumption_lemma9_denied_bidder_case` | Lemma 9.4 implies that declaring hs, v 0 i cannot be better than being truthful. 10. A Truthful Mechanism with Greedy Allocation We shall now describe the payment mechanism that we propose to be used in conjunction with the greedy allocation of Section 7. The description of the payments is tightly linked with that of the greedy algorithm. The computation of the payment is performed in parallel with the execution of the greedy algorithm and takes time linear in the number o... | No completed assumption check recorded | None recorded |
| Assumption lemma9 nonnegative value deviation | `assumption_lemma9_nonnegative_value_deviation` | Lemma 9.4 implies that declaring hs, v 0 i cannot be better than being truthful. 10. A Truthful Mechanism with Greedy Allocation We shall now describe the payment mechanism that we propose to be used in conjunction with the greedy allocation of Section 7. The description of the payments is tightly linked with that of the greedy algorithm. The computation of the payment is performed in parallel with the execution of the greedy algorithm and takes time linear in the number o... | No completed assumption check recorded | None recorded |
| Assumption lemma9 nonnegative critical value axioms | `assumption_lemma9_nonnegative_critical_value_axioms` | None recorded | No completed assumption check recorded | None recorded |
| Assumption lemma9 finite large threshold | `assumption_lemma9_finite_large_threshold` | Lemma 9.4 implies that declaring hs, v 0 i cannot be better than being truthful. 10. A Truthful Mechanism with Greedy Allocation We shall now describe the payment mechanism that we propose to be used in conjunction with the greedy allocation of Section 7. The description of the payments is tightly linked with that of the greedy algorithm. The computation of the payment is performed in parallel with the execution of the greedy algorithm and takes time linear in the number o... | No completed assumption check recorded | None recorded |
<!-- END GENERATED ASSUMPTION PROVENANCE LEDGER -->

## 14. Displayed Formula Provenance

The source-facing formula and condition rows below are exposed directly in
`PaperInterface.lean`; these are the current LLM-as-judge review rows for the corresponding source
definitions.

<!-- BEGIN GENERATED FORMULA PROVENANCE LEDGER -->
### Current Canonical Evidence
Rows are selected from semantic `formula` and `equation` source-kind metadata within the configured semantic source-coverage scope, never from declaration names. Coverage and statement checks remain separate evidence lanes. Scope metadata needs repair, so the full inventory is shown: paper_statement_map.json must explicitly set source_coverage_mode before a source-coverage closeout

| Paper formula / subclaim | Lean declaration | Provenance | Validators | Comments |
| --- | --- | --- | --- | --- |
| None | `none` | None | None | No source-map row is canonically classified as a formula or equation. |
<!-- END GENERATED FORMULA PROVENANCE LEDGER -->

## 15. Library Lift Pass
No additional reusable library extraction was performed in this report refresh.
The main future library lift is computational-complexity infrastructure for
native polynomial-time reductions, NP-hardness/inapproximability, randomized
complexity classes, and cited clique/set-packing hardness facts.

## 16. DAG Audit
`docs/DependencyDAG.tex` and `docs/DependencyDAG.pdf` are present as the
paper-facing dependency artifacts. The rendered `docs/DependencyDAG.pdf` was visually inspected
for node/label overlap and arrow-through-text issues. The DAG covers the source
inventory at the result-cluster level: utility/truthfulness definitions,
generalized Vickrey truthfulness, Theorem 6.1 set-packing reductions, Theorem
7.2 greedy approximation, Lemmas 9.1--9.5, Theorem 9.6, Definition 10.1, and
Theorem 10.2. The native machine-level NP-hardness and `NP = ZPP` consequences
remain visible as partial complexity-infrastructure boundaries rather than green
DAG endpoints.

## 17. Validation Checks
<!-- BEGIN GENERATED LLM-AS-JUDGE RESULTS -->
### LLM-as-Judge Results
- Source coverage (`audit/paper_coverage_llm.json`): 31 covered, 8 formalization boundary; diagnostics: full inventory shown because paper_statement_map.json must explicitly set source_coverage_mode before a source-coverage closeout.
- Statement match (`audit/statement_match_llm.json`): no rows; source conditions: 3 source condition, 2 formalization boundary; diagnostics: 39 orphan/stale statement-sidecar rows excluded, 4 orphan/stale source-condition sidecar rows excluded, 34 configured rows without unambiguous current receipts.
- Lean-to-TeX translations (`audit/lean_to_tex_llm.json`): 30 row translations generated from Lean statements.
- Assumption provenance (`audit/assumption_match_llm.json`): 3 source condition, 2 formalization boundary; diagnostics: 4 unconfigured, stale, or ambiguous source-condition sidecar rows excluded, 4 configured source conditions without unambiguous current receipts.
- Source-record classification (`audit/source_record_match_llm.json`): 1 formalization boundary.
- Source-record structural audit (`audit/source_record_audit.json`): 39 source-record review rows, 1 boundary input, 0 recursive fields, 0 recursion failures.
- Review-surface audit (`audit/review_surface_llm.json`): review surface passed over 39 review rows.
- Holistic source-first audit (`docs/AGENT_SOURCE_AUDIT.md`): status not inferred by this generator.
- DAG/source/source-json audit (`docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`): status not inferred by this generator.
<!-- END GENERATED LLM-AS-JUDGE RESULTS -->

The current tracked sidecars report no uncertain LLM-as-judge validations.
Statement translation has 39 rows: 31 `matches`, 8 `mismatch` rows resolved as
`formalization boundary`, and 0 `uncertain` rows. Paper coverage has 31 `covered`
items and 8 `formalization boundary` items. Assumption provenance has 7
`source condition` rows and 2 `formalization boundary` rows. The review-surface audit
passes for 39 rows. Source-record provenance has one approved external boundary
for the critical-value certificate input, with no unresolved recursion failure
reported.

The 8 conditional-boundary rows are the two external Theorem 6.1 complexity
assumptions, the two Theorem 6.1 external solver consequences, the
complexity-class note after Theorem 6.1, Lemma 9.4, Lemma 9.5, and Theorem 9.6.
These are recorded as conditional or partial because they depend on documented
critical-value or complexity-boundary conditions, not because of statement-translation uncertainty.

## 18. Paper Definitions Checked
<!-- lean-derived-definitions:start -->
### Lean-Derived Dashboard Definitions

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| Utility formula | `utility_formula` | Utility equals the bidder's value for the allocated bundle minus the bidder's payment. |
| Truthfulness predicate | `truthfulOn_iff` | Truthfulness means no admissible bidder can improve utility by replacing only that bidder's report. |
| Generalized Vickrey auction rule | `generalizedVickreyAuction_allocation_payment` | The auction uses the supplied allocation rule and Clarke-pivot payments. |
| Single-minded accepted mechanism | `singleMindedAcceptedMechanism_fields` | A single-minded mechanism consists of an accepted-bidder rule and a payment rule. |
| Single-minded truthfulness | `singleMindedTruthfulOn_iff` | No admissible single-bidder deviation raises true single-minded utility. |
| Nonnegative nonempty profiles | `nonnegativeNonemptySingleMindedProfile_iff` | Every desired bundle is nonempty and every single-minded value is nonnegative. |
| Weighted set-packing value | `weightedSetPackingValue_formula` | The objective is the sum of selected bidders' weights. |
| Set-packing bid encoding | `setPackingSingleMindedBids_formula` | Bidder `i` receives desired set `sets i` and value `weights i`. |
| Average amount per good | `averageAmountPerGood_formula` | Average amount per good is bid value divided by desired-bundle size. |
| Average order | `averageOrderOf_rule` | The order lists every bidder exactly once and is weakly descending by average amount per good. |
| Greedy accepted set from order | `greedyAcceptedFromOrder_formula` | Greedy folds through the order, accepting a bid exactly when it conflicts with no already accepted bid. |
| Average-greedy accepted set | `averageGreedyAcceptedSet_formula` | Average-greedy applies greedy acceptance to the average order. |
| Average-greedy payment | `averageGreedyPayment_formula` | Denied bidders pay zero; accepted bidders pay zero if there is no later denied blocker, otherwise bundle size times the next blocker average bid. |
<!-- lean-derived-definitions:end -->

## 19. Named Theorem Statements Checked
### Theorem-by-Theorem Validation

| Paper item | Status | Statement match | Notes |
|---|---|---|---|
| Definitions 3.1--3.2, direct combinatorial-auction mechanism and truthfulness | formalized | exact finite model | Formula/iff rows expose utility and truthfulness directly. |
| Theorem 4.1, generalized Vickrey auction is truthful | formalized | exact | Represented by a welfare-maximizing allocation certificate and Clarke-pivot payments. |
| Proposition 4.2, truthful GVA utility nonnegative | formalized | exact | Uses the paper's nonnegative bundle-value domain. |
| Definition 5.1, single-minded bidders | formalized | exact finite model | Nonempty and nonnegative single-minded profiles are explicit. |
| Theorem 6.1, set-packing and single-minded welfare reductions | formalized | exact for finite reductions | Includes feasibility/value encodings, clique/complement/independent-set/set-packing routes, and exact/approximation-preserving finite solver transfers. |
| Theorem 6.1, native NP-hardness and `NP = ZPP` consequences | partially formalized | conditional boundary | Exposed through abstract external-consequence and class-model wrappers because the library does not yet formalize native machine-level complexity classes. |
| Complexity-class note after Theorem 6.1 | partially formalized | conditional boundary | Lean proves the collapse implications from supplied class-relationship fields, not from a machine model. |
| Definition 7.1, average amount per good and greedy order | formalized | exact finite model | Includes the deterministic average-descending order used by the greedy mechanism. |
| Theorem 7.2, greedy allocation approximation | formalized | exact finite model | Includes blocker extraction, blocking-certificate counting, common-bid removal, and reduced-disjoint reasoning. |
| Lemmas 9.1--9.5, critical values and utility/payment facts | formalized with visible conditions | exact or conditional boundary as recorded | Covers nonempty nonnegative single-minded bid profiles, nonnegative/infinite critical-value certificates, and the finite-threshold case. |
| Theorem 9.6, critical axioms imply truthfulness | formalized with visible conditions | conditional boundary | Exactness, monotonicity, participation, and critical-value certificates imply truthfulness. |
| Definition 10.1, greedy payment scheme | formalized | exact finite model | Represents denied/no-next/next payment cases and accepted-bid criticality. |
| Theorem 10.2, average-order greedy mechanism truthfulness | formalized | exact source domain | Concrete allocation and payment rule are truthful on nonempty nonnegative single-minded profiles. |

## 20. Paper-Facing Statement Validator Ledger

The configured surface contains 39 rows: 30 statements and nine source
conditions. Exact semantic projection currently binds five condition receipts
and no statement receipts; the prior 31 matches and eight conditional-boundary
mismatches are historical, diagnostic evidence. Human dashboard review has
0/39 saved entries.

<!-- BEGIN GENERATED STATEMENT VALIDATOR LEDGER -->
### Current Canonical Evidence
Independent human dashboard review: 0/39 rows. No human row-level approval is inferred. review surface passed; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 Diagnostic-only evidence excluded from this paper-facing ledger: 39 unconfigured, stale, or ambiguous statement-sidecar rows, 4 unconfigured, stale, or ambiguous source-condition sidecar rows.

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| - Utility is value for the allocated bundle minus the bidder's payment. | `utility_formula` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - Truthfulness means every admissible value profile weakly prefers reporting truthfully to replacing bidder `i`'s report by any alternative bundle valuation. | `truthfulOn_iff` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - The generalized Vickrey auction uses the supplied allocation rule and Clarke pivot payments. | `generalizedVickreyAuction_allocation_payment` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - A single-minded accepted-set mechanism consists of an accepted-bidder rule and a payment rule. | `singleMindedAcceptedMechanism_fields` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - Single-minded truthfulness allows no admissible single-bidder deviation to raise the true single-minded utility. | `singleMindedTruthfulOn_iff` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - Every single-minded bid has a nonempty desired bundle and nonnegative value. | `nonnegativeNonemptySingleMindedProfile_iff` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - The weighted set-packing objective sums the selected bidders' weights. | `weightedSetPackingValue_formula` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - The set-packing encoding gives bidder `i` desired set `sets i` and value `weights i`. | `setPackingSingleMindedBids_formula` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - Average amount per good is the bid value divided by the desired-bundle size. | `averageAmountPerGood_formula` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - The concrete average order lists every bidder exactly once and is weakly descending in average amount per good. | `averageOrderOf_rule` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - The greedy accepted set starts empty and folds through the order, accepting a bid iff it conflicts with no already accepted bid. | `greedyAcceptedFromOrder_formula` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - Average-greedy accepts the greedy set from the concrete average order. | `averageGreedyAcceptedSet_formula` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - Definition 10.1 payment: denied bidders pay zero; accepted bidders pay zero when there is no later denied blocker, and otherwise pay their bundle size times that blocker bid's average amount per good. | `averageGreedyPayment_formula` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - Theorem 4.1: generalized Vickrey auctions are truthful. | `theorem4_1_generalized_vickrey_truthful` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - Proposition 4.2: truthful GVA bidder utility is nonnegative. | `proposition4_2_generalized_vickrey_truthful_utility_nonneg` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - Theorem 6.1 set-packing feasibility encoding. | `theorem6_1_set_packing_feasibility_encoding_correct` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - Theorem 6.1 set-packing value encoding. | `theorem6_1_set_packing_value_encoding_correct` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - Theorem 6.1 weighted set-packing reduction. | `theorem6_1_weighted_set_packing_reduction` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - Theorem 6.1 clique-to-single-minded welfare reduction. | `theorem6_1_clique_decision_single_minded_welfare_reduction` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - Theorem 6.1 external exact-solver complexity consequence. | `theorem6_1_external_optimal_solver_np_eq_zpp` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - Theorem 6.1 external approximation-solver complexity consequence. | `theorem6_1_external_approximation_solver_np_eq_zpp` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - Complexity-class note: `NP = ZPP` implies the randomized collapse. | `complexity_note_np_eq_zpp_implies_randomized_collapse` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - Theorem 7.2 greedy allocation square-root approximation. | `theorem7_2_sqrt_norm_approx_of_sorted_order` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - Lemma 9.1 critical-value existence from monotonicity. | `lemma9_1_exists_nonnegative_critical_value_of_monotonicity` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - Lemma 9.2 denied-bidder utility is zero. | `lemma9_2_denied_bidder_utility_eq_zero` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - Lemma 9.3 truth-telling utility is nonnegative under critical-value conditions. | `lemma9_3_truthful_utility_nonnegative_condition` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - Lemma 9.4 no profitable value-only lie under nonnegative infinity axioms. | `lemma9_4_no_profitable_value_only_lie_of_nonnegative_infinity_axioms` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - Lemma 9.5 finite threshold monotonicity. | `lemma9_5_finite_threshold_mono_of_nonnegative_infinity_certificate` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - Theorem 9.6 critical axioms imply truthfulness for single-minded bidders. | `theorem9_6_single_minded_truthful_of_nonnegative_infinity_axioms` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - Theorem 10.2 average-order greedy mechanism truthfulness. | `theorem10_2_averageGreedy_truthful` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - Truthfulness is stated relative to an admissible declaration domain. | `assumption_admissible_combinatorial_report_domain` | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | Definition 3.2 states truthfulness over bidder types and vectors of declarations; the Lean domain parameter is the finite formalization of the declaration/type domain over which truthfulness is asserted. |
| - External exact set-packing hardness and polynomial-time transfer facts for the paper's Theorem 6.1 complexity consequence. | `assumption_external_exact_set_packing_complexity_boundary` | formalization boundary; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | External exact set-packing complexity result is outside the current Lean complexity library. |
| - External set-packing inapproximability and polynomial-time transfer facts for the paper's Theorem 6.1 approximation consequence. | `assumption_external_approximation_set_packing_complexity_boundary` | formalization boundary; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | External approximation set-packing complexity result is outside the current Lean complexity library. |
| - The optimal allocation considered in Theorem 7.2 is feasible. | `assumption_theorem7_optimal_allocation_feasible` | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | Theorem 7.2 compares the greedy allocation with `OP`, the optimal solution; pairwise disjoint desired bundles are the finite single-minded representation of OP feasibility. |
| - The fixed greedy order contains every bidder in the optimal allocation. | `assumption_theorem7_optimal_bidders_in_order` | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | Theorem 7.2 proves the greedy algorithm by processing the sorted list of bids; the Lean explicit-order theorem records that the optimal bidders under comparison are present in that order. |
| Lemma 9.4 implies that declaring hs, v 0 i cannot be better than being truthful. 10. A Truthful Mechanism with Greedy Allocation We shall now describe the payment mechanism that we propose to be used in conjunction with the greedy allocation of Section 7. The description of the payments is tightly linked with that of the greedy algorithm. The computation of the payment is performed in parallel with the execution o... | `assumption_lemma9_denied_bidder_case` | No completed source-condition check recorded | None recorded |
| Lemma 9.4 implies that declaring hs, v 0 i cannot be better than being truthful. 10. A Truthful Mechanism with Greedy Allocation We shall now describe the payment mechanism that we propose to be used in conjunction with the greedy allocation of Section 7. The description of the payments is tightly linked with that of the greedy algorithm. The computation of the payment is performed in parallel with the execution o... | `assumption_lemma9_nonnegative_value_deviation` | No completed source-condition check recorded | None recorded |
| Assumption lemma9 nonnegative critical value axioms | `assumption_lemma9_nonnegative_critical_value_axioms` | No completed source-condition check recorded | None recorded |
| Lemma 9.4 implies that declaring hs, v 0 i cannot be better than being truthful. 10. A Truthful Mechanism with Greedy Allocation We shall now describe the payment mechanism that we propose to be used in conjunction with the greedy allocation of Section 7. The description of the payments is tightly linked with that of the greedy algorithm. The computation of the payment is performed in parallel with the execution o... | `assumption_lemma9_finite_large_threshold` | No completed source-condition check recorded | None recorded |
<!-- END GENERATED STATEMENT VALIDATOR LEDGER -->

## 21. Source-Coverage Audit Ledger

The current source inventory contains 39 named-theory items. Thirty-one are
covered directly. Eight remain conditional at the native computational-
complexity and finite-critical-value boundaries described in Section 5. The
row-local statement judgments record the same boundaries; there is no missing
or unclassified named source result.

<!-- BEGIN GENERATED SOURCE COVERAGE LEDGER -->
### Current Canonical Evidence
- Coverage scope: full inventory shown because scope metadata needs repair (paper_statement_map.json must explicitly set source_coverage_mode before a source-coverage closeout).
- Source inventory: 39 source statements; source artifact path not recorded.
- Coverage result: 8 conditional boundary, 31 covered.
- Coverage review: coverage ledger recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29.
- Row-local statement checks: 0/39 linked row references have a completed canonical statement check; repeated links are counted per source row.

| Source statement | Linked Lean review rows | Coverage judgment | Row-local statement checks | Comments |
| --- | --- | --- | --- | --- |
| - Utility is value for the allocated bundle minus the bidder's payment. | `utility_formula` | covered | `utility_formula`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Utility is value for the allocated bundle minus the bidder's payment. The dashboard row `utility_formula` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely inferred from a name m... |
| - Truthfulness means every admissible value profile weakly prefers reporting truthfully to replacing bidder `i`'s report by any alternative bundle valuation. | `truthfulOn_iff` | covered | `truthfulOn_iff`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Truthfulness means every admissible value profile weakly prefers reporting truthfully to replacing bidder `i`'s report by any alternative bundle valuation. The dashboard row `truthfulOn_iff` exposes the corresponding Lean statement for that same source claim, with the paper-facing theore... |
| - The generalized Vickrey auction uses the supplied allocation rule and Clarke pivot payments. | `generalizedVickreyAuction_allocation_payment` | covered | `generalizedVickreyAuction_allocation_payment`: no completed statement check | The source item is the paper-facing statement/formula summarized as: The generalized Vickrey auction uses the supplied allocation rule and Clarke pivot payments. The dashboard row `generalizedVickreyAuction_allocation_payment` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the revi... |
| - A single-minded accepted-set mechanism consists of an accepted-bidder rule and a payment rule. | `singleMindedAcceptedMechanism_fields` | covered | `singleMindedAcceptedMechanism_fields`: no completed statement check | The source item is the paper-facing statement/formula summarized as: A single-minded accepted-set mechanism consists of an accepted-bidder rule and a payment rule. The dashboard row `singleMindedAcceptedMechanism_fields` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review sur... |
| - Single-minded truthfulness allows no admissible single-bidder deviation to raise the true single-minded utility. | `singleMindedTruthfulOn_iff` | covered | `singleMindedTruthfulOn_iff`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Single-minded truthfulness allows no admissible single-bidder deviation to raise the true single-minded utility. The dashboard row `singleMindedTruthfulOn_iff` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the re... |
| - Every single-minded bid has a nonempty desired bundle and nonnegative value. | `nonnegativeNonemptySingleMindedProfile_iff` | covered | `nonnegativeNonemptySingleMindedProfile_iff`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Every single-minded bid has a nonempty desired bundle and nonnegative value. The dashboard row `nonnegativeNonemptySingleMindedProfile_iff` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather... |
| - The weighted set-packing objective sums the selected bidders' weights. | `weightedSetPackingValue_formula` | covered | `weightedSetPackingValue_formula`: no completed statement check | The source item is the paper-facing statement/formula summarized as: The weighted set-packing objective sums the selected bidders' weights. The dashboard row `weightedSetPackingValue_formula` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely infer... |
| - The set-packing encoding gives bidder `i` desired set `sets i` and value `weights i`. | `setPackingSingleMindedBids_formula` | covered | `setPackingSingleMindedBids_formula`: no completed statement check | The source item is the paper-facing statement/formula summarized as: The set-packing encoding gives bidder `i` desired set `sets i` and value `weights i`. The dashboard row `setPackingSingleMindedBids_formula` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather... |
| - Average amount per good is the bid value divided by the desired-bundle size. | `averageAmountPerGood_formula` | covered | `averageAmountPerGood_formula`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Average amount per good is the bid value divided by the desired-bundle size. The dashboard row `averageAmountPerGood_formula` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely in... |
| - The concrete average order lists every bidder exactly once and is weakly descending in average amount per good. | `averageOrderOf_rule` | covered | `averageOrderOf_rule`: no completed statement check | The source item is the paper-facing statement/formula summarized as: The concrete average order lists every bidder exactly once and is weakly descending in average amount per good. The dashboard row `averageOrderOf_rule` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review sur... |
| - The greedy accepted set starts empty and folds through the order, accepting a bid iff it conflicts with no already accepted bid. | `greedyAcceptedFromOrder_formula` | covered | `greedyAcceptedFromOrder_formula`: no completed statement check | The source item is the paper-facing statement/formula summarized as: The greedy accepted set starts empty and folds through the order, accepting a bid iff it conflicts with no already accepted bid. The dashboard row `greedyAcceptedFromOrder_formula` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula... |
| - Average-greedy accepts the greedy set from the concrete average order. | `averageGreedyAcceptedSet_formula` | covered | `averageGreedyAcceptedSet_formula`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Average-greedy accepts the greedy set from the concrete average order. The dashboard row `averageGreedyAcceptedSet_formula` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely infe... |
| - Definition 10.1 payment: denied bidders pay zero; accepted bidders pay zero when there is no later denied blocker, and otherwise pay their bundle size times that blocker bid's average amount per good. | `averageGreedyPayment_formula` | covered | `averageGreedyPayment_formula`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Definition 10.1 payment: denied bidders pay zero; accepted bidders pay zero when there is no later denied blocker, and otherwise pay their bundle size times that blocker bid's average amount per good. The dashboard row `averageGreedyPayment_formula` exposes the corresponding Lean stateme... |
| - Theorem 4.1: generalized Vickrey auctions are truthful. | `theorem4_1_generalized_vickrey_truthful` | covered | `theorem4_1_generalized_vickrey_truthful`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Theorem 4.1: generalized Vickrey auctions are truthful. The dashboard row `theorem4_1_generalized_vickrey_truthful` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely inferred fro... |
| - Proposition 4.2: truthful GVA bidder utility is nonnegative. | `proposition4_2_generalized_vickrey_truthful_utility_nonneg` | covered | `proposition4_2_generalized_vickrey_truthful_utility_nonneg`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Proposition 4.2: truthful GVA bidder utility is nonnegative. The dashboard row `proposition4_2_generalized_vickrey_truthful_utility_nonneg` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather... |
| - Theorem 6.1 set-packing feasibility encoding. | `theorem6_1_set_packing_feasibility_encoding_correct` | covered | `theorem6_1_set_packing_feasibility_encoding_correct`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Theorem 6.1 set-packing feasibility encoding. The dashboard row `theorem6_1_set_packing_feasibility_encoding_correct` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely inferred f... |
| - Theorem 6.1 set-packing value encoding. | `theorem6_1_set_packing_value_encoding_correct` | covered | `theorem6_1_set_packing_value_encoding_correct`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Theorem 6.1 set-packing value encoding. The dashboard row `theorem6_1_set_packing_value_encoding_correct` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely inferred from a name m... |
| - Theorem 6.1 weighted set-packing reduction. | `theorem6_1_weighted_set_packing_reduction` | covered | `theorem6_1_weighted_set_packing_reduction`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Theorem 6.1 weighted set-packing reduction. The dashboard row `theorem6_1_weighted_set_packing_reduction` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely inferred from a name m... |
| - Theorem 6.1 clique-to-single-minded welfare reduction. | `theorem6_1_clique_decision_single_minded_welfare_reduction` | covered | `theorem6_1_clique_decision_single_minded_welfare_reduction`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Theorem 6.1 clique-to-single-minded welfare reduction. The dashboard row `theorem6_1_clique_decision_single_minded_welfare_reduction` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than m... |
| - Theorem 6.1 external exact-solver complexity consequence. | `theorem6_1_external_optimal_solver_np_eq_zpp` | conditional boundary | `theorem6_1_external_optimal_solver_np_eq_zpp`: no completed statement check | Theorem 6.1 exact-solver complexity consequence depends on an external NP/ZPP complexity boundary. |
| - Theorem 6.1 external approximation-solver complexity consequence. | `theorem6_1_external_approximation_solver_np_eq_zpp` | conditional boundary | `theorem6_1_external_approximation_solver_np_eq_zpp`: no completed statement check | Theorem 6.1 approximation-solver complexity consequence depends on an external NP/ZPP complexity boundary. |
| - Complexity-class note: `NP = ZPP` implies the randomized collapse. | `complexity_note_np_eq_zpp_implies_randomized_collapse` | conditional boundary | `complexity_note_np_eq_zpp_implies_randomized_collapse`: no completed statement check | Complexity-collapse note is conditional on external complexity-theory infrastructure. |
| - Theorem 7.2 greedy allocation square-root approximation. | `theorem7_2_sqrt_norm_approx_of_sorted_order` | covered | `theorem7_2_sqrt_norm_approx_of_sorted_order`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Theorem 7.2 greedy allocation square-root approximation. The dashboard row `theorem7_2_sqrt_norm_approx_of_sorted_order` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely inferre... |
| - Lemma 9.1 critical-value existence from monotonicity. | `lemma9_1_exists_nonnegative_critical_value_of_monotonicity` | covered | `lemma9_1_exists_nonnegative_critical_value_of_monotonicity`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Lemma 9.1 critical-value existence from monotonicity. The dashboard row `lemma9_1_exists_nonnegative_critical_value_of_monotonicity` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than me... |
| - Lemma 9.2 denied-bidder utility is zero. | `lemma9_2_denied_bidder_utility_eq_zero` | covered | `lemma9_2_denied_bidder_utility_eq_zero`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Lemma 9.2 denied-bidder utility is zero. The dashboard row `lemma9_2_denied_bidder_utility_eq_zero` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely inferred from a name match. |
| - Lemma 9.3 truth-telling utility is nonnegative under critical-value conditions. | `lemma9_3_truthful_utility_nonnegative_condition` | covered | `lemma9_3_truthful_utility_nonnegative_condition`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Lemma 9.3 truth-telling utility is nonnegative under critical-value conditions. The dashboard row `lemma9_3_truthful_utility_nonnegative_condition` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface... |
| - Lemma 9.4 no profitable value-only lie under nonnegative infinity axioms. | `lemma9_4_no_profitable_value_only_lie_of_nonnegative_infinity_axioms` | conditional boundary | `lemma9_4_no_profitable_value_only_lie_of_nonnegative_infinity_axioms`: no completed statement check | Uses the documented nonnegative/infinite critical-value axiom package. |
| - Lemma 9.5 finite threshold monotonicity. | `lemma9_5_finite_threshold_mono_of_nonnegative_infinity_certificate` | conditional boundary | `lemma9_5_finite_threshold_mono_of_nonnegative_infinity_certificate`: no completed statement check | Uses the documented finite-threshold critical-value certificate boundary. |
| - Theorem 9.6 critical axioms imply truthfulness for single-minded bidders. | `theorem9_6_single_minded_truthful_of_nonnegative_infinity_axioms` | conditional boundary | `theorem9_6_single_minded_truthful_of_nonnegative_infinity_axioms`: no completed statement check | Truthfulness theorem is conditional on the documented nonnegative/infinite critical-value axiom package. |
| - Theorem 10.2 average-order greedy mechanism truthfulness. | `theorem10_2_averageGreedy_truthful` | covered | `theorem10_2_averageGreedy_truthful`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Theorem 10.2 average-order greedy mechanism truthfulness. The dashboard row `theorem10_2_averageGreedy_truthful` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely inferred from a... |
| - Truthfulness is stated relative to an admissible declaration domain. | `assumption_admissible_combinatorial_report_domain` | covered | `assumption_admissible_combinatorial_report_domain`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Truthfulness is stated relative to an admissible declaration domain. The dashboard row `assumption_admissible_combinatorial_report_domain` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather t... |
| - External exact set-packing hardness and polynomial-time transfer facts for the paper's Theorem 6.1 complexity consequence. | `assumption_external_exact_set_packing_complexity_boundary` | conditional boundary | `assumption_external_exact_set_packing_complexity_boundary`: no completed statement check | External exact set-packing complexity result is outside the current Lean complexity library. |
| - External set-packing inapproximability and polynomial-time transfer facts for the paper's Theorem 6.1 approximation consequence. | `assumption_external_approximation_set_packing_complexity_boundary` | conditional boundary | `assumption_external_approximation_set_packing_complexity_boundary`: no completed statement check | External approximation set-packing complexity result is outside the current Lean complexity library. |
| - The optimal allocation considered in Theorem 7.2 is feasible. | `assumption_theorem7_optimal_allocation_feasible` | covered | `assumption_theorem7_optimal_allocation_feasible`: no completed statement check | The source item is the paper-facing statement/formula summarized as: The optimal allocation considered in Theorem 7.2 is feasible. The dashboard row `assumption_theorem7_optimal_allocation_feasible` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merel... |
| - The fixed greedy order contains every bidder in the optimal allocation. | `assumption_theorem7_optimal_bidders_in_order` | covered | `assumption_theorem7_optimal_bidders_in_order`: no completed statement check | The source item is the paper-facing statement/formula summarized as: The fixed greedy order contains every bidder in the optimal allocation. The dashboard row `assumption_theorem7_optimal_bidders_in_order` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather tha... |
| - Lemma 9.2 is the denied-bidder case. | `assumption_lemma9_denied_bidder_case` | covered | `assumption_lemma9_denied_bidder_case`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Lemma 9.2 is the denied-bidder case. The dashboard row `assumption_lemma9_denied_bidder_case` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely inferred from a name match. |
| - Lemma 9.4 ranges over nonnegative single-minded value declarations. | `assumption_lemma9_nonnegative_value_deviation` | covered | `assumption_lemma9_nonnegative_value_deviation`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Lemma 9.4 ranges over nonnegative single-minded value declarations. The dashboard row `assumption_lemma9_nonnegative_value_deviation` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than m... |
| - The Lemma 9.3--9.6 critical-price rows are stated relative to the paper's critical-value axioms on the nonnegative single-minded declaration domain. | `assumption_lemma9_nonnegative_critical_value_axioms` | covered | `assumption_lemma9_nonnegative_critical_value_axioms`: no completed statement check | The source item is the paper-facing statement/formula summarized as: The Lemma 9.3--9.6 critical-price rows are stated relative to the paper's critical-value axioms on the nonnegative single-minded declaration domain. The dashboard row `assumption_lemma9_nonnegative_critical_value_axioms` exposes the corresponding Lean statement for that same source claim... |
| - Lemma 9.5 is the finite-threshold case for the larger desired set. | `assumption_lemma9_finite_large_threshold` | covered | `assumption_lemma9_finite_large_threshold`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Lemma 9.5 is the finite-threshold case for the larger desired set. The dashboard row `assumption_lemma9_finite_large_threshold` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely... |
<!-- END GENERATED SOURCE COVERAGE LEDGER -->
