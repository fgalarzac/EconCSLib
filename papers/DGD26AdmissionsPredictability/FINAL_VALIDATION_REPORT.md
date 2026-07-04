# Final Validation Report: Capacity Constraints Make Admissions Processes Less Predictable

Updated: 2026-07-03

## 1. Human Verdict
This paper's finite choice-function theory is formalized. The Lean development
covers instability, q-representative queues, sequential queue variability,
tight-instability constructions, append/remove variability, and the finite
linear-assignment extension.

No substantive theorem caveat remains in the formalized target. Empirical NYC
performance plots and private-data program instantiations are descriptive
material outside the Lean theorem scope, not unresolved mathematical
assumptions.

## 2. Closeout Status
- Completion status: formalized.
- One-sentence recap: Finite choice-function, queue-variability, and finite assignment theorem targets are formalized.
- Lean footprint: 11,553 paper-local Lean LOC; `PaperInterface.lean` is a 17-line compact entrypoint; `AuditInterface.lean` is 1,388 lines and contains the 101 configured dashboard/LLM-as-judge declarations.
- Audit summary: source coverage has 39 covered; statement LLM-as-judge has 101 matches; Lean-to-TeX has 101 row translations; assumption provenance sidecar has no rows; source-record classification has 1 validated_source_assumption; source-record audit reports 66 review rows, 1 boundary input, 0 recursion failures; review-surface audit passes over 66 review rows; holistic source-first audit PASS; DAG/source-json audit PASS in `docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`.

## 3. Source and Scope
- Paper: *Capacity Constraints Make Admissions Processes Less Predictable*
- Source version: AAAI-26 published version, DOI `10.1609/aaai.v40i45.41179`;
  TeX/formula source from arXiv `2601.11513v1`
- Lean folder: `papers/DGD26AdmissionsPredictability`
- Human-facing theorem file: `papers/DGD26AdmissionsPredictability/PaperInterface.lean`
- Row-level audit surface: `papers/DGD26AdmissionsPredictability/AuditInterface.lean`
- Paper assumption file: `papers/DGD26AdmissionsPredictability/Assumptions.lean`
- DAG artifacts: `papers/DGD26AdmissionsPredictability/docs/DependencyDAG.tex` and
  `papers/DGD26AdmissionsPredictability/docs/DependencyDAG.pdf`
- Clean LAP variability proof note:
  `papers/DGD26AdmissionsPredictability/LAP_VARIABILITY_CLEAN_PROOF.tex` and
  `papers/DGD26AdmissionsPredictability/LAP_VARIABILITY_CLEAN_PROOF.pdf`
- Lean build target: `lake build DGD26AdmissionsPredictability`

## 4. Researcher Summary of Checked Results
The formalization proves the core finite choice-function framework:
q-acceptance, choice distance, zero instability, substitutability,
monotonicity, consistency, independence, 1-instability, and the `2q`
instability upper bound.

It proves the even-instability/inconsistency result in both directions: positive
even distance after a single fresh addition yields inconsistency, and every
inconsistent feasible q-acceptant choice function has such a positive even
single-addition witness.

It proves the q-representative characterization: under feasibility,
q-representativeness is equivalent to q-acceptance, 1-instability, and
variability at most one. Exact-one refinements expose the natural nondegenerate
displacement witness rather than hiding it.

It proves the sequential-queue variability results, including additive
variability bounds for feasible q-acceptant 1-unstable stages and the
q-representative queue corollary.

It proves the finite linear-assignment results. Unique global-optimum finite
assignment selectors induce 1-unstable choice rules, and under slotwise no-ties
their variability is bounded by the number of distinct slot-induced applicant
orderings. Lean supplies the detailed alternating-splice proof behind this LAP
variability result; the public folder includes a clean paper-facing proof note
rendered as `LAP_VARIABILITY_CLEAN_PROOF.pdf`.

## 5. Remaining Boundaries and Gaps
No remaining mathematical boundary is used for the finite choice-function and
finite assignment theorem targets.

Empirical NYC performance plots and private-data program instantiations are
outside the Lean theorem scope.

## 6. Additional Assumptions Beyond Paper
None.

## 7. Proof-Strategy Deviations
None. The formalization follows the finite choice-function and finite-assignment proof routes at a source-facing level. The removable-set equality described below is a source typo, not a proof-strategy deviation.

## 8. Proof Tricks Worth Reusing
- The LAP variability proof uses a directed alternating-splice/proper-suffix
  exchange argument to make same-order-slot reasoning precise when applicants
  can be reassigned along a chain.
- Exact one-for-one changes are handled by proving no incoming edge at the fresh
  root, no outgoing edge at the lost slot, and uniqueness of the relevant
  left/right endpoints.
- Exactness claims are kept conditional on a concrete displacement witness when
  the source statement is about nonzero variability.

## 9. Mathematical Typos or Other Fixes Suggested in the Source Paper
- Appendix removable-set equality: the source appears to print `V_C(X_1) = V_C(X_1)`, while the mathematically meaningful equality used in the proof is `V_C(X_1) = V_C(X_2)`.

## 10. Paper Issues or Caveats
No substantive theorem counterexample or broader caveat is recorded. The removable-set equality above is treated as a typo.

## 11. Detailed Formalization Evidence
- Source-domain notes: the no-zero-instability result explicitly carries the
  standard nontrivial capacity domain from the source model: positive capacity
  and an applicant set larger than capacity. Exact variability and
  tight-instability refinements expose a concrete displacement witness to
  exclude degenerate no-change cases. The LAP distinct-order theorem is exposed
  with the finite assignment hypotheses used in the source proof: unique global
  chosen set, slotwise no ties, and a classifier that only groups slots with
  the same induced applicant order.
- `papers/DGD26AdmissionsPredictability/LAP.lean`: finite assignment model,
  objective optimality, alternating-splice exchange, LAP 1-instability, and the
  distinct slot-order variability theorem.
- `papers/DGD26AdmissionsPredictability/LAP_VARIABILITY_CLEAN_PROOF.pdf`: clean
  paper-facing writeup of the detailed LAP variability proof supplied by Lean.
- `papers/DGD26AdmissionsPredictability/MainTheorems.lean`: source-facing
  theorem layer.
- `papers/DGD26AdmissionsPredictability/AuditInterface.lean`: 101 dashboard
  rows for paper-facing definitions and named statements, plus 5 auxiliary
  LAP proof-support rows excluded from the public review surface.
- `EconCSLib/Foundations/Math/FiniteChoice.lean`: reusable finite choice
  function lemmas, including the even-instability inconsistency converse.

## 12. Paper Assumption Provenance
No paper-local assumption rows are tracked for this paper; the generated
validator summary above is the current assumption-provenance status. Source
model conditions are exposed directly in theorem statements and detailed
evidence.

## 13. Displayed Formula Provenance
Displayed and source-defining formulas are tracked through the paper-facing rows in `AuditInterface.lean` and the current statement-match sidecars. This report pass found no standalone formula-provenance issue beyond any source notes already listed above.

## 14. Library Lift Pass
No additional reusable library extraction was needed in this report pass.

## 15. DAG Audit
`DependencyDAG.pdf` is rendered from `DependencyDAG.tex`, uses paper-facing
statement labels rather than Lean declaration names, and was visually inspected
after PNG conversion.

## 16. Validation Checks

<!-- BEGIN GENERATED LLM-AS-JUDGE RESULTS -->
### LLM-as-Judge Results
- Source coverage (`audit/paper_coverage_llm.json`): 39 covered.
- Statement match (`audit/statement_match_llm.json`): 101 matches.
- Lean-to-TeX translations (`audit/lean_to_tex_llm.json`): 101 row translations generated from Lean statements.
- Assumption provenance (`audit/assumption_match_llm.json`): no rows.
- Source-record classification (`audit/source_record_match_llm.json`): 1 validated_source_assumption.
- Source-record structural audit (`audit/source_record_audit.json`): 66 review rows, 1 boundary input, 0 recursion failures.
- Review-surface audit (`audit/review_surface_llm.json`): passes over 66 review rows.
- Holistic source-first audit (`docs/AGENT_SOURCE_AUDIT.md`): PASS.
- DAG/source/source-json audit (`docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`): PASS.
<!-- END GENERATED LLM-AS-JUDGE RESULTS -->

- Passed: `lake build DGD26AdmissionsPredictability`
- Passed: `python3 scripts/review_dashboard.py --paper DGD26AdmissionsPredictability --statement-precheck`
  with 101/101 row-local statement translations and semantic matches current.
- Passed: `python3 scripts/review_dashboard.py --paper DGD26AdmissionsPredictability --paper-coverage-precheck`
  with 39/39 source statements covered directly and no conditional-boundary
  source items.
- Passed: `python3 scripts/review_dashboard.py --paper DGD26AdmissionsPredictability --source-to-lean-precheck`
  with 39/39 source statements linked to current Lean rows.
- Passed: recursive source-record audit with four explicit displacement-witness
  exactness conditions and no unresolved record/certificate/process boundary.
- Passed: `python3 scripts/audit_repository.py --paper DGD26AdmissionsPredictability --paper-closeout --info-limit 0`
  with 0 errors and 0 warnings.

## 17. Paper Definitions Checked
No separate generated definitions table was recorded in this report refresh. The paper-facing definition rows are tracked in `AuditInterface.lean` and the statement validator sidecars.

## 18. Named Theorem Statements Checked
No separate generated theorem table was recorded in this report refresh. Named theorem endpoints are tracked in `AuditInterface.lean`, `status.json`, and the statement validator sidecars.

## 19. Paper-Facing Statement Validator Ledger
The current LLM-as-judge sidecars are:
- `review_surface_llm.json`: current 101-row paper-facing review-surface audit.
- `lean_to_tex_llm.json`: 101 context-free Lean-to-TeX/prose translations.
- `statement_match_llm.json`: 101 semantic source-to-Lean row judgments.
- `paper_coverage_llm.json`: 39 source-inventory coverage judgments, all
  covered directly.
- `source_record_audit.json` and `source_record_match_llm.json`: recursive
  boundary/source-record audit for visible displacement-witness exactness
  premises.
