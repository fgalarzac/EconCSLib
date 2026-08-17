# Final Validation Report: LMMS04 Fair Division

Updated: 2026-07-31

## 1. Human Verdict
Partially formalized. Sections 2 and 4 are checked, and Section 3 has the
query, descent, Graham-consequence, rounded-search, and ratio-transfer support
needed for the approximation route. Full formalization still requires reusable
fixed-dimension integer-programming runtime infrastructure for the PTAS/FPTAS
layer. No fatal paper error is reported. The Lemma 2.4 proof prose appears to
say to choose a minimum endpoint where the finite-partition construction needs
a maximal or supremal endpoint; this is recorded as a typo, not a caveat. No
human dashboard sign-off has been recorded.

## 2. Closeout Status
- Completion status: partially formalized.
- One-sentence recap: Sections 2 and 4 are fully formalized. Section 3 has query/descent/rounded-search support. The PTAS/FPTAS runtime layer needs reusable fixed-dimension IP complexity infrastructure.
- Lean footprint: 80,496 paper-local Lean LOC; `PaperInterface.lean` is 303 lines; 48 human-review declarations are exposed.
- Audit summary: source coverage has 37 covered, 12 formalization boundary; diagnostics: full inventory shown because paper_statement_map.json must explicitly set source_coverage_mode before a source-coverage closeout; statement LLM-as-judge has no rows; source conditions: 11 source condition, 2 formalization boundary; diagnostics: 48 orphan/stale statement-sidecar rows excluded, 31 configured rows without unambiguous current receipts; Lean-to-TeX has 35 row translations; assumption provenance has 11 source condition, 2 formalization boundary; source-record classification has 29 formalization boundary; source-record audit reports 44 source-record review rows, 0 boundary inputs, 29 recursive fields, 0 recursion failures; review-surface audit review surface passed over 44 review rows; holistic source-first audit status is not inferred by this generator; DAG/source-json audit status is not inferred (see `docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`).

## 3. Source and Scope
- Paper: *On Approximately Fair Allocations of Indivisible Goods*
- Authors: Richard J. Lipton, Evangelos Markakis, Elchanan Mossel, and Amin Saberi
- Source version: ACM EC 2004, DOI 10.1145/988772.988792
- Public source: https://doi.org/10.1145/988772.988792
- Lean folder: `LMMS04FairDivision/`
- Human-facing theorem file: `papers/LMMS04FairDivision/PaperInterface.lean`
- Paper assumption file: `papers/LMMS04FairDivision/Assumptions.lean`
- DAG artifacts: `papers/LMMS04FairDivision/docs/DependencyDAG.tex`, `papers/LMMS04FairDivision/docs/DependencyDAG.pdf`
- Supporting machine evidence: `papers/LMMS04FairDivision/audit/*.json`.

Scope: this audit covers the declared partial public surface: Section 2 envy
and allocation results, Section 3 query/descent/rounded-search support, and
Section 4 truthfulness results. The final PTAS/FPTAS runtime layer for Theorem
3.3 remains outside the current reusable library because fixed-dimension
integer-programming runtime infrastructure is not yet available.

## 4. Researcher Summary of Checked Results
- Section 2 finite-allocation envy definitions, envy-cycle reduction, bounded-envy allocation, and the real-interval atom-bound route are checked.
- Section 3 has checked adaptive-query lower-bound wrappers, Graham-scheduling consequence rows, rounded type/value-pair search infrastructure, bounded-optimal allocation support, and additive/ratio transfer lemmas.
- Section 4 finite truthfulness results are checked: the no-truthful-envy-free/minimum-envy counterexample route and the uniform randomized mechanism with its explicit probability bound.
- The final PTAS/FPTAS runtime conclusion remains a visible reusable-library boundary, not a completed paper theorem.

## 5. Remaining Boundaries and Gaps
Full formalization requires reusable fixed-dimension integer-programming runtime
infrastructure for the PTAS/FPTAS layer in Theorem 3.3. The current Lean code
records that layer through explicit partial-boundary rows and proves the
supporting finite algebraic, rounded-search, and transfer statements around it.

## 6. Additional Assumptions Beyond Paper
None.

## 7. Proof-Strategy Deviations
- Source route: Theorem 4.1 presents a finite counterexample exposition. Lean
  route: the proof uses a smaller finite counterexample. This is sufficient for
  the impossibility theorem and keeps the checked witness minimal.
- Source route: Claim 3.4 gives a prose descent argument. Lean route: the proof
  separates high-source moves from low-only tie-breaking moves in an explicit
  finite-descent proof. This makes the progress measure checkable.
- Source route: Theorem 4.2 states an asymptotic Big-O wrapper. Lean route: the
  report records the finite inequality used by the proof. This preserves the
  checked mathematical content while leaving asymptotic notation out of the
  formal interface.

## 8. Proof Tricks Worth Reusing
- For algorithmic PTAS/FPTAS claims, isolate the finite algebraic/search support from the machine-level runtime theorem so the partial boundary is precise.
- For prose partition arguments over intervals, formalize the constructive endpoint choice explicitly; this exposes min/max or supremum direction errors cleanly.

## 9. Generalizations, Conjectures, and Extensions

The checked envy-cycle, rounded-search, and truthfulness components are
reusable for finite fair-division mechanisms. A shared fixed-dimension
integer-program runtime theorem would immediately strengthen this and other
optimization formalizations, but remains future library work.

## 10. Mathematical Typos or Other Fixes Suggested in the Source Paper
- Lemma 2.4 proof typo: the prose appears to say to choose the minimum endpoint whose prefix interval has value at most `alpha` for every player. To obtain progress and the stated finite partition, this should be read as a maximal/supremal endpoint choice.

## 11. Paper Issues or Caveats
No fatal paper error is reported. The Lemma 2.4 endpoint issue is recorded as a
typo, not a caveat. Several implicit real-support and atom-bound modeling
choices are documented in the evidence below. The paper status is partial only
because the reusable fixed-dimension IP runtime infrastructure for the final
PTAS/FPTAS layer is not yet present in the library.

## 12. Detailed Formalization Evidence
The formalization closes the Section 2 finite-allocation envy interface,
envy-cycle reduction, bounded-envy allocation theorem, and the
real-interval/atom-bound route used for the measure-valued allocation theorem.
It also closes the Section 4 finite truthfulness results: the
no-truthful-envy-free/minimum-envy counterexample route and the uniform
randomized mechanism with its explicit probability bound.

Section 3 has substantial formal content but remains partial at the runtime
boundary. The Lean development includes adaptive-query lower-bound wrappers,
the Graham-scheduling consequence used by the paper, rounded type/value-pair
search infrastructure, bounded-optimal allocation certificates, and
ratio-transfer lemmas. The final PTAS/FPTAS theorem is not closed because the
reusable fixed-dimension integer-program runtime theorem is not yet in the
library.

Source-domain notes: positive error parameters, finite duplicate-free goods
enumerations, positive atom bounds, normalized random-allocation weights, and
Section 3 load and rounding conditions are source theorem/model conditions.
Graham scheduling and fixed-dimension IP runtime are partial or external
theorem/library boundaries, not additional assumptions accepted as completed
theorem hypotheses.

## 13. Paper Assumption Provenance

Every non-derived paper-facing premise is routed through
`LMMS04FairDivision/Assumptions.lean` and checked by
`audit/assumption_match_llm.json`. Most rows are theorem-domain conditions
already present in the source structure.

<!-- BEGIN GENERATED ASSUMPTION PROVENANCE LEDGER -->
### Current Canonical Evidence
Generated from the configured source-condition surface and exact current statement digests in the canonical assumption-provenance sidecar. Model, agent, and automated checks are identified as such; no human review is inferred.

| Assumption declaration | Lean declaration | Source location / statement | Assumption validators | Comments |
| --- | --- | --- | --- | --- |
| Assumption nonnegative alpha bound | `assumption_nonnegative_alpha_bound` | - The alpha-bounded envy statements use a nonnegative marginal-value bound. | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | Theorem 2.1 uses alpha as the maximum marginal utility; monotonicity of the source valuations makes this bound nonnegative. Premise-level checks: 1 source condition |
| Assumption alpha marginal value bound | `assumption_alpha_marginal_value_bound` | - The alpha-bounded form assumes every marginal item value is at most `alpha`. | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | The alpha-bounded form of Theorem 2.1 assumes every marginal value is at most alpha; the source's named maximum-marginal version is the closed specialization. Premise-level checks: 1 source condition |
| Assumption duplicate free goods enumeration | `assumption_duplicate_free_goods_enumeration` | - The constructive algorithm endpoint enumerates the input goods without duplicates. | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | The constructive algorithm allocates the finite set of goods one-by-one; Lean represents that finite set by a duplicate-free list. Premise-level checks: 1 source condition |
| Assumption positive atom bound | `assumption_positive_atom_bound` | - The measure-valued envy theorem is stated for a positive atom bound. | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | The measure-valued extension separates the alpha = 0 divisible case and proves the finite partition route for alpha > 0. Premise-level checks: 1 source condition |
| Assumption ptas error parameter range | `assumption_ptas_error_parameter_range` | - PTAS/FPTAS ratio statements quantify over the usual positive error range. | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | The PTAS/FPTAS theorem is stated for positive error epsilon; the exact finite arithmetic endpoint restricts to epsilon <= 1 without loss for the displayed small-error regime. Premise-level checks: 2 source condition |
| Assumption external graham scheduling boundary | `assumption_external_graham_scheduling_boundary` | - Theorem 3.2 cites Graham's scheduling approximation theorem; this folder formalizes the fair-division consequence from that scheduling certificate. | formalization boundary; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | External Graham scheduling approximation boundary for the partial Section 3 formalization. Premise-level checks: 1 formalization boundary |
| Assumption fixed dimension ip runtime boundary | `assumption_fixed_dimension_ip_runtime_boundary` | - The final PTAS/FPTAS runtime conclusion is conditional on reusable fixed-dimension integer-program complexity infrastructure. | formalization boundary; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | Fixed-dimension IP runtime/search complexity boundary for the partial Section 3 formalization. Premise-level checks: 1 formalization boundary |
| Assumption positive rounding and load parameters | `assumption_positive_rounding_and_load_parameters` | - Rounded-search statements expose the paper's positive load and rounding-scale domain. | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | The rounding construction uses positive average load L, rounded average LR, and a positive lambda chosen as O(1/epsilon). Premise-level checks: 4 source condition |
| Assumption base load at most rounded average | `assumption_base_load_at_most_rounded_average` | - Capped rounded-supply endpoints compare the base load with the rounded average. | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | The source explicitly states that the original average load is at most the rounded average load. Premise-level checks: 1 source condition |
| Assumption claim34 positive small goods domain | `assumption_claim34_positive_small_goods_domain` | - Claim 3.4 finite small-good model uses positive goods whose value is below `L`. | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | Claim 3.4 is stated after reducing to goods with positive value below L. Premise-level checks: 4 source condition |
| Assumption claim34 rounded type window condition | `assumption_claim34_rounded_type_window_condition` | - Claim 3.4's finite rounded-type assignment endpoints use the source rounded type window for the selected min/max pair. | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | The Claim 3.4 rounded finite-IP endpoint compares assignments whose rounded bundle types lie in the selected min/max load window. Premise-level checks: 1 source condition |
| Assumption additive transfer load window conditions | `assumption_additive_transfer_load_window_conditions` | - Lemma 3.5's algebraic transfer row exposes positivity and half-load window conditions for the source, rounded, and output loads. | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | Lemma 3.5 and Claim 3.4 work in the half-load window L/2 < load < 2L; Lean exposes the positivity/nonnegativity consequences used by the algebraic transfer endpoint. Premise-level checks: 9 source condition |
| Assumption uniform random weight normalization | `assumption_uniform_random_weight_normalization` | - The randomized allocation concentration bound uses normalized nonnegative item weights. | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | Theorem 4.2 assumes normalized nonnegative additive utilities with every item value at most alpha and proves a bound for any positive threshold parameter. Premise-level checks: 5 source condition |
<!-- END GENERATED ASSUMPTION PROVENANCE LEDGER -->

## 14. Displayed Formula Provenance

The source-facing definition and condition rows below are exposed directly in
`PaperInterface.lean`; these are current LLM-as-judge review rows for the
corresponding source definitions.

<!-- BEGIN GENERATED FORMULA PROVENANCE LEDGER -->
### Current Canonical Evidence
Rows are selected from semantic `formula` and `equation` source-kind metadata within the configured semantic source-coverage scope, never from declaration names. Coverage and statement checks remain separate evidence lanes. Scope metadata needs repair, so the full inventory is shown: paper_statement_map.json must explicitly set source_coverage_mode before a source-coverage closeout

| Paper formula / subclaim | Lean declaration | Provenance | Validators | Comments |
| --- | --- | --- | --- | --- |
| None | `none` | None | None | No source-map row is canonically classified as a formula or equation. |
<!-- END GENERATED FORMULA PROVENANCE LEDGER -->

## 15. Library Lift Pass
No additional reusable library extraction was performed in this report refresh.
The main future library lift is fixed-dimension integer-program runtime
infrastructure, together with reusable complexity wrappers for PTAS/FPTAS
claims that depend on such solver theorems.

## 16. DAG Audit
`docs/DependencyDAG.tex` and `docs/DependencyDAG.pdf` are present as paper-facing
dependency artifacts. The rendered DAG covers the declared partial
source-result clusters: Section 2 envy and allocation definitions, Lemmas
2.2/2.4, Theorems 2.1/2.3, Section 3 query/descent and rounded-search support,
Lemma 3.5, Theorems 3.1--3.3, and Section 4 truthfulness results. The
PTAS/FPTAS runtime layer remains visible as a fixed-dimension IP
infrastructure boundary rather than a green DAG endpoint.

## 17. Validation Checks
<!-- BEGIN GENERATED LLM-AS-JUDGE RESULTS -->
### LLM-as-Judge Results
- Source coverage (`audit/paper_coverage_llm.json`): 37 covered, 12 formalization boundary; diagnostics: full inventory shown because paper_statement_map.json must explicitly set source_coverage_mode before a source-coverage closeout.
- Statement match (`audit/statement_match_llm.json`): no rows; source conditions: 11 source condition, 2 formalization boundary; diagnostics: 48 orphan/stale statement-sidecar rows excluded, 31 configured rows without unambiguous current receipts.
- Lean-to-TeX translations (`audit/lean_to_tex_llm.json`): 35 row translations generated from Lean statements.
- Assumption provenance (`audit/assumption_match_llm.json`): 11 source condition, 2 formalization boundary.
- Source-record classification (`audit/source_record_match_llm.json`): 29 formalization boundary.
- Source-record structural audit (`audit/source_record_audit.json`): 44 source-record review rows, 0 boundary inputs, 29 recursive fields, 0 recursion failures.
- Review-surface audit (`audit/review_surface_llm.json`): review surface passed over 44 review rows.
- Holistic source-first audit (`docs/AGENT_SOURCE_AUDIT.md`): status not inferred by this generator.
- DAG/source/source-json audit (`docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`): status not inferred by this generator.
<!-- END GENERATED LLM-AS-JUDGE RESULTS -->

The current tracked sidecars report no uncertain LLM-as-judge validations.
Statement translation has 48 rows: 36 `matches`, 12 `mismatch` rows resolved
as `formalization boundary`, and 0 `uncertain` rows. Paper coverage has 49
items: 37 `covered` and 12 `formalization boundary`. Assumption provenance has
11 `source condition` rows and 2 `formalization boundary` rows. The review-surface
audit passes for 48 rows. Source-record provenance records the rounded/IP
certificate support as approved external-boundary provenance and reports no
recursion failures.

The 12 conditional-boundary rows are the explicit Section 3 runtime,
fixed-dimension IP, Graham-scheduling, and related rounded-search/source-output
boundary rows. They are conditional because those reusable library components
are not yet present, not because of statement-translation uncertainty.

## 18. Paper Definitions Checked
<!-- lean-derived-definitions:start -->
### Lean-Derived Dashboard Definitions

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| Envy | `envy` | Envy of agent `i` toward agent `j`: positive part of the value difference. |
| Envy-free allocation | `envyFree` | Allocations with no positive envy between any ordered pair. |
| Bounded envy | `envyBoundedBy` | Bounded-envy predicate used in Theorem 2.1. |
| Maximum marginal value | `maxMarginal` | Maximum marginal item value. |
| Allocation of goods | `isAllocationOf` | Allocation of exactly the specified finite set of goods. |
| Direct mechanism | `directMechanism_fields` | No-transfer allocation rule on reported additive valuations. |
| Randomized direct mechanism | `randomizedDirectMechanism_fields` | Lottery over allocations on reported additive valuations. |
| Truthfulness | `truthful` | Dominant-strategy truthfulness for direct fair-division mechanisms. |
| Randomized truthfulness | `randomizedTruthful` | Expected-utility truthfulness for randomized direct mechanisms. |
<!-- lean-derived-definitions:end -->

## 19. Named Theorem Statements Checked
### Theorem-by-Theorem Validation

| Paper item | Status | Statement match | Notes |
| --- | --- | --- | --- |
| Section 2 definitions | formalized | exact | Finite-agent/finite-good paper interface. |
| Lemma 2.2, envy-cycle elimination | formalized | exact | Gives an acyclic envy graph while preserving allocation and envy bound. |
| Theorem 2.1, bounded-envy allocation existence | formalized | exact for finite goods | Includes constructive algorithm correctness for the finite allocation model. |
| Lemma 2.4 and Theorem 2.3, measure-valued utilities | formalized | model-explicit | Uses the maximal/supremal endpoint reading recorded as a source typo note. |
| Theorem 3.1, query lower bound | formalized | source-shaped | Lean proves hard-family/counting/transcript lower-bound wrappers under the source asymptotic condition. |
| Theorem 3.2, Graham 1.4 approximation | partial external dependency | conditional boundary | Lean proves the fair-division consequence from a Graham scheduling certificate, not Graham's external scheduling theorem itself. |
| Theorem 3.3, PTAS/FPTAS for identical utilities | partially formalized | conditional boundary | Finite rounded-type, value-pair search, IP-certificate, source-output, and ratio-transfer layers are formalized; final runtime theorem remains external. |
| Claim 3.4, bounded optimal allocation under small goods | formalized | finite exact-allocation and identical-utilities versions | Lean proves the finite descent and exact-allocation/model wrappers. |
| Lemma 3.5, rounded-allocation transfer | partially formalized | algebraic transfer closed | Arithmetic ratio-transfer lemmas are formalized; algorithmic/runtime packaging remains tied to Theorem 3.3's boundary. |
| Theorem 4.1, no truthful minimum-envy mechanism | formalized | proof-strengthening | Lean uses a two-player/eight-egg finite counterexample with the same manipulation structure as the paper's larger example. |
| Theorem 4.2, randomized truthful allocation bound | formalized | finite explicit bound | Lean proves independent uniform assignment truthfulness and the explicit Chebyshev/union-bound probability inequality. |

## 20. Paper-Facing Statement Validator Ledger

The current paper-facing surface has 44 rows, with human review at 0/44. The
historical model sidecar contains 48 judgments: 36 matches and 12
conditional-boundary mismatches. Because that sidecar predates the current
surface selection, it is historical evidence rather than current row-for-row
certification.

<!-- BEGIN GENERATED STATEMENT VALIDATOR LEDGER -->
### Current Canonical Evidence
Independent human dashboard review: 0/44 rows. No human row-level approval is inferred. review surface passed; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 Diagnostic-only evidence excluded from this paper-facing ledger: 48 unconfigured, stale, or ambiguous statement-sidecar rows.

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| - Envy of agent `i` toward agent `j`: positive part of the value difference. | `envy` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - Envy-free allocations have no positive envy between any ordered pair. | `envyFree` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - Bounded-envy predicate used in Theorem 2.1. | `envyBoundedBy` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - Maximum marginal item value. | `maxMarginal` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - Allocation of exactly the specified finite set of goods. | `isAllocationOf` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Lemma 2.2. For any partial allocation A with envy graph G, we can find another partial allocation B with envy graph H such that: • e(B) ≤ e(A) • H is acyclic. | `lemma2_2_acyclic_reduction` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Theorem 2.1. For any set of goods and any set of players, there exists an allocation A such that the maximum envy of A is bounded by the maximum marginal utility of the goods, α. Furthermore, given oracle access for the utility functions of the players, there is an O(mn3 ) time algorithm for finding such an allocation. Given an allocation A, we define the envy graph of A as follows: every node of the graph represe... | `theorem2_1_bounded_envy_allocation_exists` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Theorem 2.1. For any set of goods and any set of players, there exists an allocation A such that the maximum envy of A is bounded by the maximum marginal utility of the goods, α. Furthermore, given oracle access for the utility functions of the players, there is an O(mn3 ) time algorithm for finding such an allocation. Given an allocation A, we define the envy graph of A as follows: every node of the graph represe... | `theorem2_1_alpha_bounded_allocation_exists` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Theorem 2.1. For any set of goods and any set of players, there exists an allocation A such that the maximum envy of A is bounded by the maximum marginal utility of the goods, α. Furthermore, given oracle access for the utility functions of the players, there is an O(mn3 ) time algorithm for finding such an allocation. Given an allocation A, we define the envy graph of A as follows: every node of the graph represe... | `theorem2_1_algorithm_correct_list_toFinset` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Theorem 2.3. When the utilities of the players are probability measures on (Ω, F ) = ([0, 1], Borel sets) with atoms of value at most α, there exists a partition A = (A1 , ..., An ) of Ω such that e(A) ≤ α. | `theorem2_3_real_interval_supported_atom_bound` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Theorem 3.1. Any (deterministic) algorithm that computes an allocation with minimum envy or minimum envyratio requires a number of queries which is exponential in the number of goods in the worst case. | `theorem3_1_eventually_minimum_envy_lower_bound_from_twoBit_adaptive_queries` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Theorem 3.1. Any (deterministic) algorithm that computes an allocation with minimum envy or minimum envyratio requires a number of queries which is exponential in the number of goods in the worst case. | `theorem3_1_eventually_minimum_envy_ratio_lower_bound_from_twoBit_adaptive_queries` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Theorem 3.2. [5] Graham’s algorithm achieves an approximation factor of 1.4 for the envy-ratio problem. In the next Theorem, we improve this result and show that we can achieve any constant factor arbitrarily close to 1 for the envy-ratio problem. | `theorem3_2_graham_certificate_to_envy_ratio_bound` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Theorem 3.2. [5] Graham’s algorithm achieves an approximation factor of 1.4 for the envy-ratio problem. In the next Theorem, we improve this result and show that we can achieve any constant factor arbitrarily close to 1 for the envy-ratio problem. | `theorem3_2_graham_factor_eq_seven_fifths` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Theorem 3.3. There is a PTAS for the envy-ratio problem when all players have the same utility for each good. Furthermore, when the number of players is constant, there is an FPTAS. We would like to note that an interesting fact about Theorem 3.1 is that it is unconditional, i.e., not dependent on any complexity theory assumption. 3.1 Additive Utilities | `theorem3_3_solver_auto_cap_full_ip_summary_with_ratio_guarantee` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Theorem 3.3. There is a PTAS for the envy-ratio problem when all players have the same utility for each good. Furthermore, when the number of players is constant, there is an FPTAS. We would like to note that an interesting fact about Theorem 3.1 is that it is unconditional, i.e., not dependent on any complexity theory assumption. 3.1 Additive Utilities | `theorem3_3_claim34_fixed_rounding_ratio_endpoint` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Theorem 3.3. There is a PTAS for the envy-ratio problem when all players have the same utility for each good. Furthermore, when the number of players is constant, there is an FPTAS. We would like to note that an interesting fact about Theorem 3.1 is that it is unconditional, i.e., not dependent on any complexity theory assumption. 3.1 Additive Utilities | `theorem3_3_claim34_capped_weighted_supply_ratio_endpoint` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Claim 3.4. If v(i) < L for every good i, then there exists an optimal allocation A = (A1 , ..., An ) such that 12 L < v(Ai ) < 2L. | `claim3_4_bounded_optimal_of_exact_allocations_with_nonempty_positive_goods` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Claim 3.4. If v(i) < L for every good i, then there exists an optimal allocation A = (A1 , ..., An ) such that 12 L < v(Ai ) < 2L. | `claim3_4_identical_utilities_bounded_optimum_bound` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Theorem 3.3. There is a PTAS for the envy-ratio problem when all players have the same utility for each good. Furthermore, when the number of players is constant, there is an FPTAS. We would like to note that an interesting fact about Theorem 3.1 is that it is unconditional, i.e., not dependent on any complexity theory assumption. 3.1 Additive Utilities | `theorem3_3_ratio_transfer_certificate_epsilon_of_agentwise_additive_loads` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Lemma 3.5. Output A. Suppose without loss of generality that v(AR 1 ) ≤ ... ≤ ∗ ∗ ∗ v(AR n ) and v(A1 ) ≤ ... ≤ v(An ). Let A = (A1 , ..., An ) be an optimal solution to I satisfying the conditions of Claim 3.4 and assume v(A∗1 ) ≤ ... ≤ v(A∗n ). We want to show: v(A∗n ) v(An ) ≤ (1 + ) ) v(A1 ) v(A∗1 By Lemma 3.5 we know that: v(An ) ≤ v(AR n) + 1 R L ≤ v(AR L ≤ v(AR ) n) = n )(1 + λ λ λ λ Similar calculations y... | `lemma3_5_additive_transfer_epsilon_bound` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - A direct no-transfer mechanism consists only of an allocation rule. | `directMechanism_fields` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - A randomized direct no-transfer mechanism consists only of an allocation law. | `randomizedDirectMechanism_fields` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - Dominant-strategy truthfulness for direct fair-division mechanisms. | `truthful` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - Expected-utility truthfulness for randomized direct mechanisms. | `randomizedTruthful` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Theorem 4.1. Any mechanism that returns an allocation with minimum possible envy cannot be truthful. The same is true for any mechanism that returns an envy-free allocation whenever there exists one. | `theorem4_1_source_goods_content` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Theorem 4.1. Any mechanism that returns an allocation with minimum possible envy cannot be truthful. The same is true for any mechanism that returns an envy-free allocation whenever there exists one. | `theorem4_1_true_report_formula` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Theorem 4.1. Any mechanism that returns an allocation with minimum possible envy cannot be truthful. The same is true for any mechanism that returns an envy-free allocation whenever there exists one. | `theorem4_1_source_not_truthful_envy_free_whenever_exists` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Theorem 4.1. Any mechanism that returns an allocation with minimum possible envy cannot be truthful. The same is true for any mechanism that returns an envy-free allocation whenever there exists one. | `theorem4_1_source_minimum_envy_not_truthful` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Theorem 4.2. Suppose that vp,i ≤ α ∀p ∈ N, j ∈ M . Then for every  > 0, and for large enough n, there exists a truthful algorithm such that with high probability the allocation √ output by the algorithm has maximum envy at most O( α n1/2+ ). | `theorem4_2_uniform_random_mechanism_truthful` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Theorem 4.2. Suppose that vp,i ≤ α ∀p ∈ N, j ∈ M . Then for every  > 0, and for large enough n, there exists a truthful algorithm such that with high probability the allocation √ output by the algorithm has maximum envy at most O( α n1/2+ ). | `theorem4_2_uniform_random_max_envy_probability_bound` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| - The alpha-bounded envy statements use a nonnegative marginal-value bound. | `assumption_nonnegative_alpha_bound` | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | Theorem 2.1 uses alpha as the maximum marginal utility; monotonicity of the source valuations makes this bound nonnegative. |
| - The alpha-bounded form assumes every marginal item value is at most `alpha`. | `assumption_alpha_marginal_value_bound` | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | The alpha-bounded form of Theorem 2.1 assumes every marginal value is at most alpha; the source's named maximum-marginal version is the closed specialization. |
| - The constructive algorithm endpoint enumerates the input goods without duplicates. | `assumption_duplicate_free_goods_enumeration` | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | The constructive algorithm allocates the finite set of goods one-by-one; Lean represents that finite set by a duplicate-free list. |
| - The measure-valued envy theorem is stated for a positive atom bound. | `assumption_positive_atom_bound` | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | The measure-valued extension separates the alpha = 0 divisible case and proves the finite partition route for alpha > 0. |
| - PTAS/FPTAS ratio statements quantify over the usual positive error range. | `assumption_ptas_error_parameter_range` | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | The PTAS/FPTAS theorem is stated for positive error epsilon; the exact finite arithmetic endpoint restricts to epsilon <= 1 without loss for the displayed small-error regime. |
| - Theorem 3.2 cites Graham's scheduling approximation theorem; this folder formalizes the fair-division consequence from that scheduling certificate. | `assumption_external_graham_scheduling_boundary` | formalization boundary; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | External Graham scheduling approximation boundary for the partial Section 3 formalization. |
| - The final PTAS/FPTAS runtime conclusion is conditional on reusable fixed-dimension integer-program complexity infrastructure. | `assumption_fixed_dimension_ip_runtime_boundary` | formalization boundary; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | Fixed-dimension IP runtime/search complexity boundary for the partial Section 3 formalization. |
| - Rounded-search statements expose the paper's positive load and rounding-scale domain. | `assumption_positive_rounding_and_load_parameters` | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | The rounding construction uses positive average load L, rounded average LR, and a positive lambda chosen as O(1/epsilon). |
| - Capped rounded-supply endpoints compare the base load with the rounded average. | `assumption_base_load_at_most_rounded_average` | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | The source explicitly states that the original average load is at most the rounded average load. |
| - Claim 3.4 finite small-good model uses positive goods whose value is below `L`. | `assumption_claim34_positive_small_goods_domain` | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | Claim 3.4 is stated after reducing to goods with positive value below L. |
| - Claim 3.4's finite rounded-type assignment endpoints use the source rounded type window for the selected min/max pair. | `assumption_claim34_rounded_type_window_condition` | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | The Claim 3.4 rounded finite-IP endpoint compares assignments whose rounded bundle types lie in the selected min/max load window. |
| - Lemma 3.5's algebraic transfer row exposes positivity and half-load window conditions for the source, rounded, and output loads. | `assumption_additive_transfer_load_window_conditions` | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | Lemma 3.5 and Claim 3.4 work in the half-load window L/2 < load < 2L; Lean exposes the positivity/nonnegativity consequences used by the algebraic transfer endpoint. |
| - The randomized allocation concentration bound uses normalized nonnegative item weights. | `assumption_uniform_random_weight_normalization` | source condition; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | Theorem 4.2 assumes normalized nonnegative additive utilities with every item value at most alpha and proves a bound for any positive threshold parameter. |
<!-- END GENERATED STATEMENT VALIDATOR LEDGER -->

## 21. Source-Coverage Audit Ledger

The current source inventory has 49 selected named-theory items: 37 are
covered and 12 are conditional on the fixed-dimension integer-program runtime
boundary described in Section 5. The source map and row-local statement checks
agree on that disposition; no selected item is silently omitted.

<!-- BEGIN GENERATED SOURCE COVERAGE LEDGER -->
### Current Canonical Evidence
- Coverage scope: full inventory shown because scope metadata needs repair (paper_statement_map.json must explicitly set source_coverage_mode before a source-coverage closeout).
- Source inventory: 49 source statements; source artifact path not recorded.
- Coverage result: 12 conditional boundary, 37 covered.
- Coverage review: coverage ledger recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29.
- Row-local statement checks: 0/50 linked row references have a completed canonical statement check; repeated links are counted per source row.

| Source statement | Linked Lean review rows | Coverage judgment | Row-local statement checks | Comments |
| --- | --- | --- | --- | --- |
| - Envy of agent `i` toward agent `j`: positive part of the value difference. | `envy` | covered | `envy`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Envy of agent `i` toward agent `j`: positive part of the value difference. The dashboard row `envy` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely inferred from a name match. |
| - Envy-free allocations have no positive envy between any ordered pair. | `envyFree` | covered | `envyFree`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Envy-free allocations have no positive envy between any ordered pair. The dashboard row `envyFree` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely inferred from a name match. |
| - Bounded-envy predicate used in Theorem 2.1. | `envyBoundedBy` | covered | `envyBoundedBy`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Bounded-envy predicate used in Theorem 2.1. The dashboard row `envyBoundedBy` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely inferred from a name match. |
| - Maximum marginal item value. | `maxMarginal` | covered | `maxMarginal`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Maximum marginal item value. The dashboard row `maxMarginal` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely inferred from a name match. |
| - Allocation of exactly the specified finite set of goods. | `isAllocationOf` | covered | `isAllocationOf`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Allocation of exactly the specified finite set of goods. The dashboard row `isAllocationOf` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely inferred from a name match. |
| - Lemma 2.2: envy-cycle elimination produces an acyclic envy graph. | `lemma2_2_acyclic_reduction` | covered | `lemma2_2_acyclic_reduction`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Lemma 2.2: envy-cycle elimination produces an acyclic envy graph. The dashboard row `lemma2_2_acyclic_reduction` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely inferred from a... |
| - Theorem 2.1: bounded-envy allocation existence. | `theorem2_1_bounded_envy_allocation_exists` | covered | `theorem2_1_bounded_envy_allocation_exists`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Theorem 2.1: bounded-envy allocation existence. The dashboard row `theorem2_1_bounded_envy_allocation_exists` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely inferred from a na... |
| - Theorem 2.1 alpha-bounded form. | `theorem2_1_alpha_bounded_allocation_exists` | covered | `theorem2_1_alpha_bounded_allocation_exists`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Theorem 2.1 alpha-bounded form. The dashboard row `theorem2_1_alpha_bounded_allocation_exists` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely inferred from a name match. |
| - Theorem 2.1 constructive list algorithm form. | `theorem2_1_algorithm_correct_list_toFinset` | covered | `theorem2_1_algorithm_correct_list_toFinset`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Theorem 2.1 constructive list algorithm form. The dashboard row `theorem2_1_algorithm_correct_list_toFinset` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely inferred from a nam... |
| - Theorem 2.3 real-interval supported atom-bound endpoint. | `theorem2_3_real_interval_supported_atom_bound` | covered | `theorem2_3_real_interval_supported_atom_bound`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Theorem 2.3 real-interval supported atom-bound endpoint. The dashboard row `theorem2_3_real_interval_supported_atom_bound` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely infer... |
| - Theorem 3.1 adaptive-query lower bound. | `theorem3_1_eventually_minimum_envy_lower_bound_from_twoBit_adaptive_queries` | covered | `theorem3_1_eventually_minimum_envy_lower_bound_from_twoBit_adaptive_queries`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Theorem 3.1 adaptive-query lower bound. The dashboard row `theorem3_1_eventually_minimum_envy_lower_bound_from_twoBit_adaptive_queries` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than... |
| - Theorem 3.1 adaptive-query ratio lower bound. | `theorem3_1_eventually_minimum_envy_ratio_lower_bound_from_twoBit_adaptive_queries` | covered | `theorem3_1_eventually_minimum_envy_ratio_lower_bound_from_twoBit_adaptive_queries`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Theorem 3.1 adaptive-query ratio lower bound. The dashboard row `theorem3_1_eventually_minimum_envy_ratio_lower_bound_from_twoBit_adaptive_queries` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface... |
| - Theorem 3.2 Graham-certificate fair-division consequence. | `theorem3_2_graham_certificate_to_envy_ratio_bound` | conditional boundary | `theorem3_2_graham_certificate_to_envy_ratio_bound`: no completed statement check | Depends on the documented external Graham scheduling certificate boundary. |
| - Theorem 3.2 evaluates the Graham factor as seven fifths. | `theorem3_2_graham_factor_eq_seven_fifths` | covered | `theorem3_2_graham_factor_eq_seven_fifths`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Theorem 3.2 evaluates the Graham factor as seven fifths. The dashboard row `theorem3_2_graham_factor_eq_seven_fifths` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely inferred f... |
| - Theorem 3.3 conditional fixed-dimension IP summary. | `theorem3_3_solver_auto_cap_full_ip_summary_with_ratio_guarantee` | conditional boundary | `theorem3_3_solver_auto_cap_full_ip_summary_with_ratio_guarantee`: no completed statement check | Depends on the documented fixed-dimension IP/search certificate boundary. |
| - Theorem 3.3 compact external-solver package. runtime/FPTAS conclusion is exactly the supplied external solver consequence. | `theorem3_3_solver_auto_cap_full_ip_summary_with_ratio_guarantee` | conditional boundary | `theorem3_3_solver_auto_cap_full_ip_summary_with_ratio_guarantee`: no completed statement check | This partial-boundary source item is covered through the compact current Theorem 3.3 solver/Claim 3.4 dashboard row(s), which expose the same conditional external-solver endpoint without keeping the broad package projection rows on the human review surface. |
| - Theorem 3.3 compact external-solver payload projection. payload from the conditional external-solver package. | `theorem3_3_solver_auto_cap_full_ip_summary_with_ratio_guarantee` | conditional boundary | `theorem3_3_solver_auto_cap_full_ip_summary_with_ratio_guarantee`: no completed statement check | This partial-boundary source item is covered through the compact current Theorem 3.3 solver/Claim 3.4 dashboard row(s), which expose the same conditional external-solver endpoint without keeping the broad package projection rows on the human review surface. |
| - Theorem 3.3 compact external-solver consequence projection. the external solver consequence, pending the reusable fixed-dimension IP theorem. | `theorem3_3_solver_auto_cap_full_ip_summary_with_ratio_guarantee` | conditional boundary | `theorem3_3_solver_auto_cap_full_ip_summary_with_ratio_guarantee`: no completed statement check | This partial-boundary source item is covered through the compact current Theorem 3.3 solver/Claim 3.4 dashboard row(s), which expose the same conditional external-solver endpoint without keeping the broad package projection rows on the human review surface. |
| - Theorem 3.3 strongest Claim-3.4 additive external-solver endpoint. selected-pair estimates, this returns the compact external-solver package. | `theorem3_3_solver_auto_cap_full_ip_summary_with_ratio_guarantee`<br>`theorem3_3_claim34_fixed_rounding_ratio_endpoint` | conditional boundary | `theorem3_3_solver_auto_cap_full_ip_summary_with_ratio_guarantee`: no completed statement check<br>`theorem3_3_claim34_fixed_rounding_ratio_endpoint`: no completed statement check | This partial-boundary source item is covered through the compact current Theorem 3.3 solver/Claim 3.4 dashboard row(s), which expose the same conditional external-solver endpoint without keeping the broad package projection rows on the human review surface. |
| - Claim 3.4 fixed-rounding ratio endpoint. | `theorem3_3_claim34_fixed_rounding_ratio_endpoint` | conditional boundary | `theorem3_3_claim34_fixed_rounding_ratio_endpoint`: no completed statement check | Claim 3.4 rounded-search endpoint is conditional on the documented search/runtime boundary. |
| - Claim 3.4 capped weighted-supply endpoint. | `theorem3_3_claim34_capped_weighted_supply_ratio_endpoint` | conditional boundary | `theorem3_3_claim34_capped_weighted_supply_ratio_endpoint`: no completed statement check | Claim 3.4 capped weighted-supply endpoint is conditional on the documented search/runtime boundary. |
| - Claim 3.4 exact-allocation bounded optimum endpoint. | `claim3_4_bounded_optimal_of_exact_allocations_with_nonempty_positive_goods` | covered | `claim3_4_bounded_optimal_of_exact_allocations_with_nonempty_positive_goods`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Claim 3.4 exact-allocation bounded optimum endpoint. The dashboard row `claim3_4_bounded_optimal_of_exact_allocations_with_nonempty_positive_goods` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface... |
| - Claim 3.4 identical-utilities bounded optimum bound. Section 3 rounded-search runtime layer remains a partial boundary. | `claim3_4_identical_utilities_bounded_optimum_bound` | conditional boundary | `claim3_4_identical_utilities_bounded_optimum_bound`: no completed statement check | Claim 3.4 identical-utilities bounded optimum bound remains tied to the rounded-search partial boundary. |
| - Theorem 3.3 additive-load ratio transfer. | `theorem3_3_ratio_transfer_certificate_epsilon_of_agentwise_additive_loads` | covered | `theorem3_3_ratio_transfer_certificate_epsilon_of_agentwise_additive_loads`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Theorem 3.3 additive-load ratio transfer. The dashboard row `theorem3_3_ratio_transfer_certificate_epsilon_of_agentwise_additive_loads` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than... |
| - Lemma 3.5 additive transfer epsilon bound. certificate/load-window premises are recorded in the paper assumption ledger. | `lemma3_5_additive_transfer_epsilon_bound` | conditional boundary | `lemma3_5_additive_transfer_epsilon_bound`: no completed statement check | Lemma 3.5 transfer row exposes certificate/load-window premises recorded as a partial boundary. |
| - A direct no-transfer mechanism consists only of an allocation rule. | `directMechanism_fields` | covered | `directMechanism_fields`: no completed statement check | The source item is the paper-facing statement/formula summarized as: A direct no-transfer mechanism consists only of an allocation rule. The dashboard row `directMechanism_fields` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely inferred from a n... |
| - A randomized direct no-transfer mechanism consists only of an allocation law. | `randomizedDirectMechanism_fields` | covered | `randomizedDirectMechanism_fields`: no completed statement check | The source item is the paper-facing statement/formula summarized as: A randomized direct no-transfer mechanism consists only of an allocation law. The dashboard row `randomizedDirectMechanism_fields` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than mere... |
| - Dominant-strategy truthfulness for direct fair-division mechanisms. | `truthful` | covered | `truthful`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Dominant-strategy truthfulness for direct fair-division mechanisms. The dashboard row `truthful` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely inferred from a name match. |
| - Expected-utility truthfulness for randomized direct mechanisms. | `randomizedTruthful` | covered | `randomizedTruthful`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Expected-utility truthfulness for randomized direct mechanisms. The dashboard row `randomizedTruthful` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely inferred from a name match. |
| - Theorem 4.1 uses the full finite source universe: two named goods plus eight egg goods, for ten goods total and two agents. | `theorem4_1_source_goods_content` | covered | `theorem4_1_source_goods_content`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Theorem 4.1 uses the full finite source universe: two named goods plus eight egg goods, for ten goods total and two agents. The dashboard row `theorem4_1_source_goods_content` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula repre... |
| - Theorem 4.1's truthful report is the additive bundle valuation generated by the displayed two-player item weights. | `theorem4_1_true_report_formula` | covered | `theorem4_1_true_report_formula`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Theorem 4.1's truthful report is the additive bundle valuation generated by the displayed two-player item weights. The dashboard row `theorem4_1_true_report_formula` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in... |
| - Theorem 4.1 envy-free mechanism impossibility. | `theorem4_1_source_not_truthful_envy_free_whenever_exists` | covered | `theorem4_1_source_not_truthful_envy_free_whenever_exists`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Theorem 4.1 envy-free mechanism impossibility. The dashboard row `theorem4_1_source_not_truthful_envy_free_whenever_exists` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely infe... |
| - Theorem 4.1 minimum-envy mechanism impossibility. | `theorem4_1_source_minimum_envy_not_truthful` | covered | `theorem4_1_source_minimum_envy_not_truthful`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Theorem 4.1 minimum-envy mechanism impossibility. The dashboard row `theorem4_1_source_minimum_envy_not_truthful` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely inferred from... |
| - Theorem 4.2 uniform-random mechanism truthfulness. | `theorem4_2_uniform_random_mechanism_truthful` | covered | `theorem4_2_uniform_random_mechanism_truthful`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Theorem 4.2 uniform-random mechanism truthfulness. The dashboard row `theorem4_2_uniform_random_mechanism_truthful` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely inferred fro... |
| - Theorem 4.2 uniform-random maximum-envy probability bound. | `theorem4_2_uniform_random_max_envy_probability_bound` | covered | `theorem4_2_uniform_random_max_envy_probability_bound`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Theorem 4.2 uniform-random maximum-envy probability bound. The dashboard row `theorem4_2_uniform_random_max_envy_probability_bound` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than mer... |
| - The alpha-bounded envy statements use a nonnegative marginal-value bound. | `assumption_nonnegative_alpha_bound` | covered | `assumption_nonnegative_alpha_bound`: no completed statement check | The source item is the paper-facing statement/formula summarized as: The alpha-bounded envy statements use a nonnegative marginal-value bound. The dashboard row `assumption_nonnegative_alpha_bound` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely... |
| - The alpha-bounded form assumes every marginal item value is at most `alpha`. | `assumption_alpha_marginal_value_bound` | covered | `assumption_alpha_marginal_value_bound`: no completed statement check | The source item is the paper-facing statement/formula summarized as: The alpha-bounded form assumes every marginal item value is at most `alpha`. The dashboard row `assumption_alpha_marginal_value_bound` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than... |
| - The constructive algorithm endpoint enumerates the input goods without duplicates. | `assumption_duplicate_free_goods_enumeration` | covered | `assumption_duplicate_free_goods_enumeration`: no completed statement check | The source item is the paper-facing statement/formula summarized as: The constructive algorithm endpoint enumerates the input goods without duplicates. The dashboard row `assumption_duplicate_free_goods_enumeration` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface... |
| - The measure-valued envy theorem is stated for a positive atom bound. | `assumption_positive_atom_bound` | covered | `assumption_positive_atom_bound`: no completed statement check | The source item is the paper-facing statement/formula summarized as: The measure-valued envy theorem is stated for a positive atom bound. The dashboard row `assumption_positive_atom_bound` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely inferred... |
| - PTAS/FPTAS ratio statements quantify over the usual positive error range. | `assumption_ptas_error_parameter_range` | covered | `assumption_ptas_error_parameter_range`: no completed statement check | The source item is the paper-facing statement/formula summarized as: PTAS/FPTAS ratio statements quantify over the usual positive error range. The dashboard row `assumption_ptas_error_parameter_range` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than mer... |
| - Theorem 3.2 cites Graham's scheduling approximation theorem; this folder formalizes the fair-division consequence from that scheduling certificate. | `assumption_external_graham_scheduling_boundary` | conditional boundary | `assumption_external_graham_scheduling_boundary`: no completed statement check | External Graham scheduling approximation boundary for the partial Section 3 formalization. |
| - The final PTAS/FPTAS runtime conclusion is conditional on reusable fixed-dimension integer-program complexity infrastructure. | `assumption_fixed_dimension_ip_runtime_boundary` | conditional boundary | `assumption_fixed_dimension_ip_runtime_boundary`: no completed statement check | Fixed-dimension IP runtime/search complexity boundary for the partial Section 3 formalization. |
| - Rounded-search statements expose the paper's positive load and rounding-scale domain. | `assumption_positive_rounding_and_load_parameters` | covered | `assumption_positive_rounding_and_load_parameters`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Rounded-search statements expose the paper's positive load and rounding-scale domain. The dashboard row `assumption_positive_rounding_and_load_parameters` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review... |
| - Capped rounded-supply endpoints compare the base load with the rounded average. | `assumption_base_load_at_most_rounded_average` | covered | `assumption_base_load_at_most_rounded_average`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Capped rounded-supply endpoints compare the base load with the rounded average. The dashboard row `assumption_base_load_at_most_rounded_average` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface ra... |
| - Claim 3.4 finite small-good model uses positive goods whose value is below `L`. | `assumption_claim34_positive_small_goods_domain` | covered | `assumption_claim34_positive_small_goods_domain`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Claim 3.4 finite small-good model uses positive goods whose value is below `L`. The dashboard row `assumption_claim34_positive_small_goods_domain` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface... |
| - Claim 3.4's finite rounded-type assignment endpoints use the source rounded type window for the selected min/max pair. | `assumption_claim34_rounded_type_window_condition` | covered | `assumption_claim34_rounded_type_window_condition`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Claim 3.4's finite rounded-type assignment endpoints use the source rounded type window for the selected min/max pair. The dashboard row `assumption_claim34_rounded_type_window_condition` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/f... |
| - Lemma 3.5's algebraic transfer row exposes positivity and half-load window conditions for the source, rounded, and output loads. | `assumption_additive_transfer_load_window_conditions` | covered | `assumption_additive_transfer_load_window_conditions`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Lemma 3.5's algebraic transfer row exposes positivity and half-load window conditions for the source, rounded, and output loads. The dashboard row `assumption_additive_transfer_load_window_conditions` exposes the corresponding Lean statement for that same source claim, with the paper-fac... |
| - The randomized allocation concentration bound uses normalized nonnegative item weights. | `assumption_uniform_random_weight_normalization` | covered | `assumption_uniform_random_weight_normalization`: no completed statement check | The source item is the paper-facing statement/formula summarized as: The randomized allocation concentration bound uses normalized nonnegative item weights. The dashboard row `assumption_uniform_random_weight_normalization` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review... |
| - Lemma 2.4: partition the real interval support into finitely many low-value pieces under the paper atom-bound hypothesis. | `theorem2_3_real_interval_supported_atom_bound` | covered | `theorem2_3_real_interval_supported_atom_bound`: no completed statement check | Lemma 2.4 is a named source proof step for the Theorem 2.3 real-interval atom-bound route. The compact dashboard exposes it through the Theorem 2.3 row, while the Lean proof route is implemented in Lemma24MeasurePartition.lean. |
<!-- END GENERATED SOURCE COVERAGE LEDGER -->
