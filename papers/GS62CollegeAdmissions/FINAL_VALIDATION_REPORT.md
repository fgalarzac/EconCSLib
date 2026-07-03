# Final Validation Report: Gale-Shapley 1962

Updated: 2026-07-03

## 1. Human Verdict
Formalized. The Gale-Shapley existence, college-admissions existence, and
applicant-optimality results are checked using the shared matching library. No
paper-correctness caveat is reported. No human dashboard sign-off has been
recorded.

## 2. Closeout Status
- Completion status: formalized.
- One-sentence recap: This only uses a few lines of code as its infrastructure has largely been elevated to the shared matching library.
- Lean footprint: 388 paper-local Lean LOC; `PaperInterface.lean` is 116 lines; 7 human-review declarations are exposed.
- Audit summary: source coverage has 7 covered; statement LLM-as-judge has 7 matches; Lean-to-TeX has 7 row translations; assumption provenance sidecar is not tracked; source-record classification sidecar is not tracked; source-record audit reports 7 review rows, 0 boundary inputs, 0 recursion failures; review-surface audit passes over 7 review rows; holistic source-first audit PASS; DAG/source-json audit PASS in `docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`.

## 3. Source and Scope
- Paper: *College Admissions and the Stability of Marriage*
- Authors: D. Gale and L. S. Shapley
- Source version: *The American Mathematical Monthly*, Vol. 69, No. 1
  (January 1962), pp. 9--15; DOI
  https://doi.org/10.1080/00029890.1962.11989827; stable JSTOR URL
  http://www.jstor.org/stable/2312726
- Lean folder: `papers/GS62CollegeAdmissions`
- Human-facing theorem file: `papers/GS62CollegeAdmissions/PaperInterface.lean`
- Audit ledger: `papers/GS62CollegeAdmissions/PostPaperAudit.lean`
- DAG artifacts: `papers/GS62CollegeAdmissions/docs/DependencyDAG.tex`,
  `papers/GS62CollegeAdmissions/docs/DependencyDAG.pdf`

## 4. Researcher Summary of Checked Results
- The formalization checks the Gale-Shapley stable-marriage theorem, the college-admissions existence theorem, and applicant-optimality.
- The proof uses the shared matching library while preserving the paper's strict-preference matching domain.
- No source-paper caveat is recorded for the checked results.

## 5. Remaining Boundaries and Gaps
None.

## 6. Additional Assumptions Beyond Paper
None.

## 7. Proof-Strategy Deviations
None. The deferred-acceptance reuse, cloned-seat quota construction, and
proposer-optimality reuse are proof-organization choices recorded below, not
substantive departures from the Gale-Shapley proof route.

## 8. Proof Tricks Worth Reusing
- Reuse the shared deferred-acceptance stability and proposer-optimality theorems for older matching papers with terse source proofs.
- Treat many-to-one college quotas through cloned seats when the source proof explicitly reduces college admissions to strict marriage markets.
- Keep finite equal-cardinality completeness bridges small and source-facing so the reusable matching layer remains general.

## 9. Mathematical Typos or Other Fixes Suggested in the Source Paper
None found.

## 10. Paper Issues or Caveats
None found.

## 11. Detailed Formalization Evidence
Proof-organization notes:

- Theorem 1 is discharged through the reusable deferred-acceptance stability
  theorem plus a finite equal-cardinality completeness bridge.
- The college-admissions quota theorem uses the source-standard cloned-seat
  reduction for college quotas.
- Theorem 2 uses the reusable deferred-acceptance proposer-optimality theorem
  already developed for the shared matching library.

## 12. Paper Assumption Provenance
| Assumption declaration | Lean declaration | Source location / statement | Assumption validators | Comments |
| --- | --- | --- | --- | --- |
| None | `none` | None | None | No explicit paper-assumption premises remain; equal cardinality is derived from the same-index finite representation. |

- `gs_strict_marriage_domain`: packages strict rankings, all-pairs
  acceptability, and outside-option value `0`. These are explicit Lean
  versions of the paper's marriage-market conventions.
- Finite `Fintype`/`DecidableEq` instances: Lean bookkeeping for the finite
  applicant, college, and cloned-seat sets used by the constructive algorithm.
- Responsive cloned-seat college preferences: the many-to-one theorem treats a
  college's quota as identical seats with the same applicant ranking. This is
  the standard cloned-seat formalization of the paper's college quota model.

## 13. Displayed Formula Provenance
Displayed and source-defining formulas are tracked through the paper-facing rows in `PaperInterface.lean` and the current statement-match sidecars. This report pass found no standalone formula-provenance issue beyond any source notes already listed above.

## 14. Library Lift Pass
The main reusable material already lives in the shared matching library: deferred-acceptance stability, proposer-optimality, side-swapping, and finite strict-marriage infrastructure. No additional extraction was needed for this report pass.

## 15. DAG Audit
`DependencyDAG.tex` and `DependencyDAG.pdf` are present. The public holistic DAG audit reports PASS for the GS62 DAG/source/source-json comparison: the formalized source-facing endpoints are represented, and the quota result is shown through the verified deferred-acceptance/cloned-seat reduction.

## 16. Validation Checks

<!-- BEGIN GENERATED LLM-AS-JUDGE RESULTS -->
### LLM-as-Judge Results
- Source coverage (`audit/paper_coverage_llm.json`): 7 covered.
- Statement match (`audit/statement_match_llm.json`): 7 matches.
- Lean-to-TeX translations (`audit/lean_to_tex_llm.json`): 7 row translations generated from Lean statements.
- Assumption provenance: no assumption-match sidecar tracked for this paper.
- Source-record classification: no source-record classification sidecar tracked for this paper.
- Source-record structural audit (`audit/source_record_audit.json`): 7 review rows, 0 boundary inputs, 0 recursion failures.
- Review-surface audit (`audit/review_surface_llm.json`): passes over 7 review rows.
- Holistic source-first audit (`docs/AGENT_SOURCE_AUDIT.md`): PASS.
- DAG/source/source-json audit (`docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`): PASS.
<!-- END GENERATED LLM-AS-JUDGE RESULTS -->

### Cross-Artifact Checks

- Paper text/PDF: local PDF/text caches are ignored by the paper-folder
  `.gitignore`; the attempted text extraction produced only metadata.
- README: every claimed named source endpoint has a controlled-vocabulary status
  row and explicit modeling notes.
- DAG: every closed source-facing endpoint is green, and the general quota node
  depends by a solid verified edge on the reusable deferred-acceptance layer.
  The rendered DAG was visually inspected after regeneration.
- Lean: `PostPaperAudit.lean` is imported by the paper root module and exposes
  one audit theorem for each final endpoint.

### Verification Checks

- The local text extraction had no OCR content, so named-result checking used
  the cached scan and public OCR snippets.
- The paper root module imports `PaperInterface.lean`, `MainTheorems.lean`, and
  `PostPaperAudit.lean`.
- The paper Lean target builds successfully, and the rendered DAG was visually
  inspected after regeneration.

### Statement Translation Audit

Audit date: 2026-06-29.
Scope: current dashboard surface from `PaperInterface.lean`; the generated
LLM-as-judge block above is sourced from the tracked sidecars.

Summary: statement match has 7 matches; Lean-to-TeX has 7 row translations; assumption provenance has no assumption-match sidecar tracked.
No separate stale manual validator table is maintained in this report.

## 17. Paper Definitions Checked
<!-- lean-derived-definitions:start -->
### Lean-Derived Dashboard Definitions

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| def strictMarriageDomain | `strictMarriageDomain` | - Strict marriage domain: both sides have strict preferences and every possible man-woman pair is acceptable. |
| def stableMarriage | `stableMarriage` | - Stable marriage: individual rationality for both sides and no blocking pair. |
| def completeMarriage | `completeMarriage` | - Complete marriage: every participant is matched. |
| def applicantOptimalStableMarriage | `applicantOptimalStableMarriage` | - Applicant/proposer optimal stable marriage: every proposer weakly prefers this stable marriage to any other stable marriage. |
<!-- lean-derived-definitions:end -->

## 18. Named Theorem Statements Checked
### Theorem-by-Theorem Validation

| Paper item | Lean declaration | Status | Statement match | Notes |
|---|---|---|---|---|
| Stable marriage definition | `gs_stable_marriage` | fully formalized | exact up to explicit source-domain assumptions | The Lean model makes the source stability condition explicit over finite sides and outside option value `0`. |
| Complete marriage definition | `gs_complete_marriage` | fully formalized | exact up to explicit source-domain assumptions | Completeness represents the paper's no-unmatched marriage convention. |
| Applicant-optimal stable assignment definition | `gs_applicant_optimal_stable_marriage` | fully formalized | exact up to explicit source-domain assumptions | The definition states applicant-side weak optimality among stable assignments. |
| Strict marriage-domain convention | `gs_strict_marriage_domain` | fully formalized | minor deviation | Lean packages strict rankings and all-pairs acceptability explicitly. |
| Theorem 1: stable marriages exist | `audit_theorem1_stable_marriage_exists` | fully formalized | exact up to explicit source-domain assumptions | The statement is exposed and discharged by the closed reusable deferred-acceptance stability theorem plus finite completeness. |
| College-admissions stable assignment with finite quotas | `audit_college_admissions_stable_assignment_exists` | fully formalized | minor deviation | The cloned-seat route compiles against the closed many-to-one stability endpoint. |
| Theorem 2: applicants are at least as well off under the procedure as under any other stable assignment | `audit_theorem2_deferred_acceptance_applicant_optimal` | fully formalized | exact up to explicit source-domain assumptions | Proposer optimality is discharged through the closed reusable DA optimality theorem. |

<!-- lean-derived-statements:start -->
### Lean-Derived Dashboard Named Statements

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| theorem theorem1_stable_marriage_exists | `theorem1_stable_marriage_exists` | - Theorem 1: on the strict same-index finite marriage domain, a stable complete marriage exists. |
| theorem college_admissions_stable_assignment_exists | `college_admissions_stable_assignment_exists` | - College-admissions theorem: finite applicants and colleges with arbitrary quotas and applicant/college utilities admit a stable many-to-one assignment. |
| theorem theorem2_applicant_optimality | `theorem2_applicant_optimality` | - Theorem 2: on the finite same-index strict marriage domain, the applicant-proposing deferred-acceptance assignment is complete and applicant-optimal among stable assignments. |
<!-- lean-derived-statements:end -->

## 19. Paper-Facing Statement Validator Ledger
Current source: `audit/statement_match_llm.json`, refreshed 2026-06-29.

| Validator surface | Result |
| --- | --- |
| Statement match | 7 matches. |
| Lean-to-TeX drafts | 7 row translations generated from Lean statements. |
| Assumption provenance | no assumption-match sidecar tracked. |
| Source coverage | 7 covered. |

The full row-level validator ledger is tracked in the JSON sidecars. Human
dashboard reviews and model/agent statement checks are separate provenance lanes;
this report does not change the human-only `human_review.reviewed_rows` counter.
