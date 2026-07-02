# Final Validation Report: LMMS04 Fair Division

Updated: 2026-07-02

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
- Audit summary: paper coverage has 37 covered, 12 conditional_boundary; statement LLM-as-judge has 36 matches, 12 mismatch; resolutions: 12 conditional_boundary; assumption provenance has 11 paper_condition, 2 partial_boundary; source-record audit reports 0 boundary inputs and 0 recursion failures; review-surface audit passes; holistic source-first audit PASS; DAG/source-json audit PASS in `docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`.

## 3. Source and Scope
- Paper: *On Approximately Fair Allocations of Indivisible Goods*
- Authors: Richard J. Lipton, Evangelos Markakis, Elchanan Mossel, and Amin Saberi
- Source version: ACM EC 2004, DOI 10.1145/988772.988792
- Lean folder: `LMMS04FairDivision/`
- Human-facing theorem file: `LMMS04FairDivision/PaperInterface.lean`
- Paper assumption file: `LMMS04FairDivision/Assumptions.lean`
- DAG artifacts: `LMMS04FairDivision/docs/DependencyDAG.tex`, `LMMS04FairDivision/docs/DependencyDAG.pdf`
- Supporting audit ledgers: `LMMS04FairDivision/docs/POST_FORMALIZATION_AUDIT.md`, `LMMS04FairDivision/AGENT_SOURCE_AUDIT.md`, and `LMMS04FairDivision/audit/*.json`

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
None. Positive error parameters, finite duplicate-free goods enumerations,
positive atom bounds, normalized random-allocation weights, and Section 3 load
and rounding conditions are source theorem/model conditions. Graham scheduling
and fixed-dimension IP runtime are partial or external theorem/library
boundaries, not additional assumptions accepted as completed theorem
hypotheses.

## 7. Proof-Strategy Deviations
- Theorem 4.1 is proved with a smaller finite counterexample than the source exposition; this is sufficient for the impossibility theorem.
- Claim 3.4 required a more explicit finite-descent proof than the prose presentation. The formal proof separates high-source moves from low-only tie-breaking moves.
- Theorem 4.2 is recorded as the finite inequality used by the proof rather than a separate asymptotic Big-O wrapper.

## 8. Proof Tricks Worth Reusing
- For algorithmic PTAS/FPTAS claims, isolate the finite algebraic/search support from the machine-level runtime theorem so the partial boundary is precise.
- For prose partition arguments over intervals, formalize the constructive endpoint choice explicitly; this exposes min/max or supremum direction errors cleanly.

## 9. Mathematical Typos or Other Fixes Suggested in the Source Paper
- Lemma 2.4 proof typo: the prose appears to say to choose the minimum endpoint whose prefix interval has value at most `alpha` for every player. To obtain progress and the stated finite partition, this should be read as a maximal/supremal endpoint choice.

## 10. Paper Issues or Caveats
No fatal paper error is reported. The Lemma 2.4 endpoint issue is recorded as a
typo, not a caveat. Several implicit real-support and atom-bound modeling
choices are documented in the evidence below. The paper status is partial only
because the reusable fixed-dimension IP runtime infrastructure for the final
PTAS/FPTAS layer is not yet present in the library.

## 11. Detailed Formalization Evidence
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

## 12. Paper Assumption Provenance
Every non-derived paper-facing premise is routed through
`LMMS04FairDivision/Assumptions.lean` and checked by
`audit/assumption_match_llm.json`. Most rows are theorem-domain conditions
already present in the source structure.

| Lean assumption/condition | Judgment | Source role |
| --- | --- | --- |
| `assumption_nonnegative_alpha_bound` | paper condition | Nonnegative alpha for bounded-envy finite allocations. |
| `assumption_alpha_marginal_value_bound` | paper condition | Alpha bounds maximum marginal item value in Theorem 2.1. |
| `assumption_duplicate_free_goods_enumeration` | paper condition | Constructive algorithm list enumerates the finite good set. |
| `assumption_positive_atom_bound` | paper condition | Positive atom-size bound for Theorem 2.3/Lemma 2.4. |
| `assumption_ptas_error_parameter_range` | paper condition | Positive PTAS/FPTAS error parameter with finite wrapper range. |
| `assumption_external_graham_scheduling_boundary` | partial boundary | Graham scheduling theorem is cited externally by the source paper; Lean proves the fair-division consequence from it. |
| `assumption_fixed_dimension_ip_runtime_boundary` | partial boundary | Fixed-dimension IP runtime theorem remains reusable library infrastructure work. |
| `assumption_positive_rounding_and_load_parameters` | paper condition | Positive load and rounding parameters in Section 3. |
| `assumption_base_load_at_most_rounded_average` | paper condition | Capped rounded-supply helper domain. |
| `assumption_claim34_positive_small_goods_domain` | paper condition | Claim 3.4 small-good model domain. |
| `assumption_claim34_rounded_type_window_condition` | paper condition | Rounded-type window condition for Claim 3.4 support. |
| `assumption_additive_transfer_load_window_conditions` | paper condition | Lemma 3.5 load-window transfer conditions. |
| `assumption_uniform_random_weight_normalization` | paper condition | Theorem 4.2 normalized nonnegative additive utilities. |

## 13. Displayed Formula Provenance
The source-facing definition and condition rows below are exposed directly in
`PaperInterface.lean`; these are current LLM-as-judge review rows for the
corresponding source definitions.

| Paper formula or condition | Lean declaration | Provenance status |
| --- | --- | --- |
| Envy of one agent toward another. | `envy` | exact definition row |
| Envy-free allocation. | `envyFree` | exact definition row |
| Bounded-envy predicate. | `envyBoundedBy` | exact definition row |
| Maximum marginal item value. | `maxMarginal` | exact definition row |
| Allocation of a finite good set. | `isAllocationOf` | exact definition row |
| Direct and randomized direct mechanisms. | `directMechanism_fields`, `randomizedDirectMechanism_fields` | exact structure rows |
| Truthfulness and randomized truthfulness. | `truthful`, `randomizedTruthful` | exact condition rows |

## 14. Library Lift Pass
No additional reusable library extraction was performed in this report refresh.
The main future library lift is fixed-dimension integer-program runtime
infrastructure, together with reusable complexity wrappers for PTAS/FPTAS
claims that depend on such solver theorems.

## 15. DAG Audit
`DependencyDAG.tex` and `DependencyDAG.pdf` are present as paper-facing
dependency artifacts. The rendered DAG covers the declared partial
source-result clusters: Section 2 envy and allocation definitions, Lemmas
2.2/2.4, Theorems 2.1/2.3, Section 3 query/descent and rounded-search support,
Lemma 3.5, Theorems 3.1--3.3, and Section 4 truthfulness results. The
PTAS/FPTAS runtime layer remains visible as a fixed-dimension IP
infrastructure boundary rather than a green DAG endpoint.

## 16. Validation Checks
The current tracked sidecars report no uncertain LLM-as-judge validations.
Statement translation has 48 rows: 36 `matches`, 12 `mismatch` rows resolved
as `conditional_boundary`, and 0 `uncertain` rows. Paper coverage has 49
items: 37 `covered` and 12 `conditional_boundary`. Assumption provenance has
11 `paper_condition` rows and 2 `partial_boundary` rows. The review-surface
audit passes for 48 rows. Source-record provenance records the rounded/IP
certificate support as approved external-boundary provenance and reports no
recursion failures.

The 12 conditional-boundary rows are the explicit Section 3 runtime,
fixed-dimension IP, Graham-scheduling, and related rounded-search/source-output
boundary rows. They are conditional because those reusable library components
are not yet present, not because of statement-translation uncertainty.

## 17. Paper Definitions Checked
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

## 18. Named Theorem Statements Checked
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

## 19. Paper-Facing Statement Validator Ledger
Current model-validator sidecars are the source of truth for timestamped rows.
Human dashboard review has 0 of 48 saved entries. Model review has 36 matches
and 12 conditional-boundary mismatches; there are no uncertain model rows and
no stale sidecar rows.

| Review group | Model review | Comment |
| --- | --- | --- |
| Section 2 definitions and allocation theorems | match | Envy/allocation definitions, envy-cycle reduction, bounded-envy allocation, and real-interval atom-bound route. |
| Section 3 lower-bound and Graham consequence rows | match or conditional boundary | Query lower-bound support is checked; Graham scheduling remains an external cited theorem. |
| Section 3 PTAS/FPTAS and rounded-search rows | conditional-boundary mismatch | Fixed-dimension IP runtime and selected source-output/runtime packaging remain partial boundaries. |
| Claim 3.4 and Lemma 3.5 support rows | match or conditional boundary | Finite descent and algebraic transfer rows are checked; algorithmic packaging remains boundary-tied. |
| Section 4 truthfulness rows | match | Finite counterexample and uniform randomized mechanism truthfulness/probability rows are checked. |
