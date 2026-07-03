# Final Validation Report: LOS02 Combinatorial Auctions

Updated: 2026-07-03

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
- Audit summary: source coverage has 31 covered, 8 conditional_boundary; statement LLM-as-judge has 31 matches, 8 mismatch; resolutions: 8 conditional_boundary; Lean-to-TeX has 30 row translations; assumption provenance has 7 paper_condition, 2 partial_boundary; source-record classification has 1 approved_external_boundary; source-record audit reports 39 review rows, 1 boundary input, 0 recursion failures; review-surface audit passes over 39 review rows; holistic source-first audit PASS; DAG/source-json audit PASS in `docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`.

## 3. Source and Scope
- Paper: *Truth Revelation in Approximately Efficient Combinatorial Auctions*
- Authors: Daniel Lehmann, Liadan Ita O'Callaghan, and Yoav Shoham
- Source version: Journal of the ACM 49(5), 2002
- Lean folder: `LOS02CombinatorialAuctions/`
- Human-facing theorem file: `LOS02CombinatorialAuctions/PaperInterface.lean`
- Paper assumption file: `LOS02CombinatorialAuctions/Assumptions.lean`
- DAG artifacts: `LOS02CombinatorialAuctions/docs/DependencyDAG.tex`, `LOS02CombinatorialAuctions/docs/DependencyDAG.pdf`
- Supporting audit ledgers: `LOS02CombinatorialAuctions/docs/POST_FORMALIZATION_AUDIT.md`, `LOS02CombinatorialAuctions/docs/AGENT_SOURCE_AUDIT.md`, and `LOS02CombinatorialAuctions/audit/*.json`

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

## 9. Mathematical Typos or Other Fixes Suggested in the Source Paper
None found.

## 10. Paper Issues or Caveats
No auction-theoretic paper error is reported. The paper status is partial only
because the reusable computational-complexity infrastructure for the final
native complexity claims is not yet present in the library.

## 11. Detailed Formalization Evidence
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

## 12. Paper Assumption Provenance
Every paper-facing premise is routed through
`LOS02CombinatorialAuctions/Assumptions.lean` and checked by
`audit/assumption_match_llm.json`. The auction-theoretic premises below are
source conditions; the Theorem 6.1 complexity rows are documented
partial-formalization boundaries.

| Lean assumption/condition | Judgment | Source role |
| --- | --- | --- |
| `assumption_admissible_combinatorial_report_domain` | source condition | Definition 3.2 truthfulness is stated over true bidder types and declaration vectors. |
| `assumption_theorem7_optimal_allocation_feasible` | source condition | Theorem 7.2 compares greedy with `OP`, the optimal feasible allocation. |
| `assumption_theorem7_optimal_bidders_in_order` | source condition | Theorem 7.2 processes the sorted bid list containing the optimal bids under comparison. |
| `assumption_lemma9_denied_bidder_case` | source condition | Lemma 9.2 is exactly the denied-bidder case. |
| `assumption_lemma9_nonnegative_value_deviation` | source condition | Single-minded value deviations stay in the nonnegative source declaration domain. |
| `assumption_lemma9_nonnegative_critical_value_axioms` | source condition | Lemmas 9.3--9.6 use the paper's critical-value and infinity-case conditions. |
| `assumption_lemma9_finite_large_threshold` | source condition | Lemma 9.5 handles the finite critical-price comparison for the larger desired set. |
| `assumption_external_exact_set_packing_complexity_boundary` | partial boundary | External Karp/Hastad-style hardness and polynomial-time transfer facts. |
| `assumption_external_approximation_set_packing_complexity_boundary` | partial boundary | External inapproximability and randomized-complexity consequence facts. |

## 13. Displayed Formula Provenance
The source-facing formula and condition rows below are exposed directly in
`PaperInterface.lean`; these are the current LLM-as-judge review rows for the corresponding source
definitions.

| Paper formula or condition | Lean declaration | Provenance status |
| --- | --- | --- |
| Utility is value for the allocated bundle minus payment. | `utility_formula` | exact formula row |
| Truthfulness is no profitable unilateral report deviation on the admissible domain. | `truthfulOn_iff` | exact iff row |
| Generalized Vickrey allocation and Clarke-pivot payment rule. | `generalizedVickreyAuction_allocation_payment` | exact formula row |
| Single-minded accepted-set mechanism fields. | `singleMindedAcceptedMechanism_fields` | exact structure row |
| Single-minded truthfulness is no profitable admissible single-bidder deviation. | `singleMindedTruthfulOn_iff` | exact iff row |
| Nonempty desired bundle and nonnegative value for each single-minded bid. | `nonnegativeNonemptySingleMindedProfile_iff` | exact condition row |
| Weighted set-packing objective sums selected weights. | `weightedSetPackingValue_formula` | exact formula row |
| Set-packing bids encode each bidder's desired set and value. | `setPackingSingleMindedBids_formula` | exact formula row |
| Average amount per good is value divided by desired-bundle size. | `averageAmountPerGood_formula` | exact formula row |
| Average order lists all bidders once and descends by average amount per good. | `averageOrderOf_rule` | exact rule row |
| Greedy acceptance folds through the order and accepts non-conflicting bids. | `greedyAcceptedFromOrder_formula` | exact formula row |
| Average-greedy accepted set applies greedy acceptance to the average order. | `averageGreedyAcceptedSet_formula` | exact formula row |
| Definition 10.1 payment rule for denied/no-next/next-blocker cases. | `averageGreedyPayment_formula` | exact formula row |

## 14. Library Lift Pass
No additional reusable library extraction was performed in this report refresh.
The main future library lift is computational-complexity infrastructure for
native polynomial-time reductions, NP-hardness/inapproximability, randomized
complexity classes, and cited clique/set-packing hardness facts.

## 15. DAG Audit
`DependencyDAG.tex` and `DependencyDAG.pdf` are present as the paper-facing
dependency artifacts. The rendered `DependencyDAG.pdf` was visually inspected
for node/label overlap and arrow-through-text issues. The DAG covers the source
inventory at the result-cluster level: utility/truthfulness definitions,
generalized Vickrey truthfulness, Theorem 6.1 set-packing reductions, Theorem
7.2 greedy approximation, Lemmas 9.1--9.5, Theorem 9.6, Definition 10.1, and
Theorem 10.2. The native machine-level NP-hardness and `NP = ZPP` consequences
remain visible as partial complexity-infrastructure boundaries rather than green
DAG endpoints.

## 16. Validation Checks

<!-- BEGIN GENERATED LLM-AS-JUDGE RESULTS -->
### LLM-as-Judge Results
- Source coverage (`audit/paper_coverage_llm.json`): 31 covered, 8 conditional_boundary.
- Statement match (`audit/statement_match_llm.json`): 31 matches, 8 mismatch; resolutions: 8 conditional_boundary.
- Lean-to-TeX translations (`audit/lean_to_tex_llm.json`): 30 row translations generated from Lean statements.
- Assumption provenance (`audit/assumption_match_llm.json`): 7 paper_condition, 2 partial_boundary.
- Source-record classification (`audit/source_record_match_llm.json`): 1 approved_external_boundary.
- Source-record structural audit (`audit/source_record_audit.json`): 39 review rows, 1 boundary input, 0 recursion failures.
- Review-surface audit (`audit/review_surface_llm.json`): passes over 39 review rows.
- Holistic source-first audit (`docs/AGENT_SOURCE_AUDIT.md`): PASS.
- DAG/source/source-json audit (`docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`): PASS.
<!-- END GENERATED LLM-AS-JUDGE RESULTS -->

The current tracked sidecars report no uncertain LLM-as-judge validations.
Statement translation has 39 rows: 31 `matches`, 8 `mismatch` rows resolved as
`conditional_boundary`, and 0 `uncertain` rows. Paper coverage has 31 `covered`
items and 8 `conditional_boundary` items. Assumption provenance has 7
`paper_condition` rows and 2 `partial_boundary` rows. The review-surface audit
passes for 39 rows. Source-record provenance has one approved external boundary
for the critical-value certificate input, with no unresolved recursion failure
reported.

The 8 conditional-boundary rows are the two external Theorem 6.1 complexity
assumptions, the two Theorem 6.1 external solver consequences, the
complexity-class note after Theorem 6.1, Lemma 9.4, Lemma 9.5, and Theorem 9.6.
These are recorded as conditional or partial because they depend on documented
critical-value or complexity-boundary conditions, not because of statement-translation uncertainty.

## 17. Paper Definitions Checked
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

## 18. Named Theorem Statements Checked
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

## 19. Paper-Facing Statement Validator Ledger
Current model-validator sidecars are the source of truth for the rows below.
Human dashboard review has 0/39 saved entries. Model review has 31 matches and
8 conditional-boundary mismatches; there are no uncertain rows and no stale
sidecar rows.

| Review row | Model review | Comment |
| --- | --- | --- |
| `utility_formula` | match | Direct utility formula. |
| `truthfulOn_iff` | match | Direct truthfulness condition. |
| `generalizedVickreyAuction_allocation_payment` | match | Allocation and Clarke-pivot payment rule. |
| `singleMindedAcceptedMechanism_fields` | match | Accepted-set mechanism fields. |
| `singleMindedTruthfulOn_iff` | match | Single-minded truthfulness condition. |
| `nonnegativeNonemptySingleMindedProfile_iff` | match | Nonnegative/nonempty source domain. |
| `weightedSetPackingValue_formula` | match | Weighted set-packing objective formula. |
| `setPackingSingleMindedBids_formula` | match | Set-packing bid encoding. |
| `averageAmountPerGood_formula` | match | Definition 7.1 average bid formula. |
| `averageOrderOf_rule` | match | Average-descending order rule. |
| `greedyAcceptedFromOrder_formula` | match | Greedy acceptance fold. |
| `averageGreedyAcceptedSet_formula` | match | Average-greedy accepted set. |
| `averageGreedyPayment_formula` | match | Definition 10.1 payment formula. |
| `theorem4_1_generalized_vickrey_truthful` | match | Generalized Vickrey truthfulness. |
| `proposition4_2_generalized_vickrey_truthful_utility_nonneg` | match | Nonnegative truthful utility. |
| `theorem6_1_set_packing_feasibility_encoding_correct` | match | Set-packing feasibility encoding. |
| `theorem6_1_set_packing_value_encoding_correct` | match | Set-packing value encoding. |
| `theorem6_1_weighted_set_packing_reduction` | match | Weighted set-packing reduction. |
| `theorem6_1_clique_decision_single_minded_welfare_reduction` | match | Clique-to-single-minded welfare reduction. |
| `theorem6_1_external_optimal_solver_np_eq_zpp` | conditional-boundary mismatch | Depends on external exact set-packing complexity infrastructure. |
| `theorem6_1_external_approximation_solver_np_eq_zpp` | conditional-boundary mismatch | Depends on external approximation set-packing complexity infrastructure. |
| `complexity_note_np_eq_zpp_implies_randomized_collapse` | conditional-boundary mismatch | Conditional on external complexity-theory infrastructure. |
| `theorem7_2_sqrt_norm_approx_of_sorted_order` | match | Greedy square-root approximation. |
| `lemma9_1_exists_nonnegative_critical_value_of_monotonicity` | match | Critical-value existence from monotonicity. |
| `lemma9_2_denied_bidder_utility_eq_zero` | match | Denied-bidder utility is zero. |
| `lemma9_3_truthful_utility_nonnegative_condition` | match | Truthful utility is nonnegative under critical-value conditions. |
| `lemma9_4_no_profitable_value_only_lie_of_nonnegative_infinity_axioms` | conditional-boundary mismatch | Uses documented nonnegative/infinite critical-value axiom package. |
| `lemma9_5_finite_threshold_mono_of_nonnegative_infinity_certificate` | conditional-boundary mismatch | Uses documented finite-threshold critical-value certificate boundary. |
| `theorem9_6_single_minded_truthful_of_nonnegative_infinity_axioms` | conditional-boundary mismatch | Conditional on documented critical-value axiom package. |
| `theorem10_2_averageGreedy_truthful` | match | Average-greedy truthfulness. |
| `assumption_admissible_combinatorial_report_domain` | match | Source domain condition. |
| `assumption_theorem7_optimal_allocation_feasible` | match | Source optimal-allocation comparison condition. |
| `assumption_theorem7_optimal_bidders_in_order` | match | Source sorted-order comparison condition. |
| `assumption_lemma9_denied_bidder_case` | match | Source denied-bidder case. |
| `assumption_lemma9_nonnegative_value_deviation` | match | Source nonnegative-value deviation domain. |
| `assumption_lemma9_nonnegative_critical_value_axioms` | match | Source critical-value axiom package. |
| `assumption_lemma9_finite_large_threshold` | match | Source finite-threshold case. |
| `assumption_external_exact_set_packing_complexity_boundary` | conditional-boundary mismatch | External exact complexity boundary. |
| `assumption_external_approximation_set_packing_complexity_boundary` | conditional-boundary mismatch | External approximation complexity boundary. |
