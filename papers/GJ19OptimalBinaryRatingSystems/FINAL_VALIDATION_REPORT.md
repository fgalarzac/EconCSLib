# Final Validation Report: GJ19 Optimal Binary Rating Systems

Updated: 2026-07-03

## 1. Human Verdict
The binary-rating theory from the AISTATS/PMLR paper and supplement is
formalized in Lean. The checked surface covers the finite large-deviation
layer, Theorem 3.1, Theorem 3.2 certificate statements, Appendix B convergence
and learning lemmas, and the Kendall/Spearman example branches. No source
discrepancy is identified for this theorem surface.

## 2. Closeout Status
- Completion status: formalized.
- One-sentence recap: The report records the current formalization status and validation evidence for the declared paper surface.
- Lean footprint: 85,780 paper-local Lean LOC; `PaperInterface.lean` is 12481 lines; 56 human-review declarations are exposed.
- Audit summary: source coverage has 27 covered, 1 covered_by_support; statement LLM-as-judge has 56 matches; Lean-to-TeX has 56 row translations; assumption provenance sidecar is not tracked; source-record classification has 2 validated_source_assumption; source-record audit reports 56 review rows, 2 boundary inputs, 0 recursion failures; review-surface audit passes over 56 review rows; holistic source-first audit PASS; DAG/source-json audit PASS in `docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`.

## 3. Source and Scope
- Paper: *Designing Optimal Binary Rating Systems*.
- Authors: Nikhil Garg and Ramesh Johari.
- Publication venue: AISTATS / PMLR 89, 2019.
- Source version: PMLR 89 paper PDF plus PMLR supplement PDF.
- Lean folder: `papers/GJ19OptimalBinaryRatingSystems`.
- Human-facing theorem file: `papers/GJ19OptimalBinaryRatingSystems/PaperInterface.lean`.
- Detailed audit: `papers/GJ19OptimalBinaryRatingSystems/docs/POST_FORMALIZATION_AUDIT.md`.
- DAG artifacts: `papers/GJ19OptimalBinaryRatingSystems/docs/DependencyDAG.tex`, `papers/GJ19OptimalBinaryRatingSystems/docs/DependencyDAG.pdf`.

The source PDF, supplement, TeX, and extracted text caches are local
source-audit artifacts. They are not part of the committed theorem surface.
Empirical simulations, figures, and visualization material are outside the
Lean theorem scope.

## 4. Researcher Summary of Checked Results
The formalization verifies the paper's mathematical theory for optimal binary
rating systems. The checked development includes Bernoulli KL formulas,
adjacent-rate formulas, finite equalized-rate optimization, finite and
continuum objective aggregation, the large-deviation rate characterization, the
algorithmic certificate layer, Appendix B convergence and learning statements,
and the Kendall/Spearman examples.

## 5. Remaining Boundaries and Gaps
No remaining theorem boundary is recorded for the formalized mathematical
surface. Empirical simulations, plots, and visualization material remain
outside the Lean theorem scope.

## 6. Additional Assumptions Beyond Paper
None.

## 7. Proof-Strategy Deviations
None. The Lean proof factors several source arguments through reusable large-deviation, finite-optimization, and convergence interfaces, but the paper-facing conclusions are the source results.

## 8. Proof Tricks Worth Reusing
- Keep displayed formulas as small review rows before exposing broad theorem
  wrappers.
- Separate source-level theorem rows from helper rows so the dashboard remains
  reviewable.
- Package reusable regularity reductions in a paper-local assumptions/proof
  interface rather than turning them into public caveats.

## 9. Mathematical Typos or Other Fixes Suggested in the Source Paper
None found.

## 10. Paper Issues or Caveats
None recorded for the formalized theorem surface.

## 11. Detailed Formalization Evidence
The formalized surface includes:

- Bernoulli KL and support-safe Bernoulli KL formulas.
- Theorem 3.1 adjacent binary-rate formula and two-stage value/rate optimality
  logic.
- Lemma 3.1 closed adjacent-rate formula and finite equalized-rate optimizer.
- Theorem C.1 weighted large-deviation/Laplace skeleton.
- Lemma C.3 finite decomposition, adjacent dominance, and partition-integral
  aggregation.
- Lemma C.4 positive-rate characterization and reverse obstruction.
- Theorem 3.2 finite calculated-grid approximation/runtime certificate
  statements.
- Lemmas C.10-C.12, the Kendall/Spearman examples, Theorem B.1, Corollary C.4,
  and Appendix B.2/B.3 learning wrappers.

Source-domain notes: the Lean development exposes model-regularity,
measurability, boundedness, positivity, and convergence hypotheses explicitly
where the source proof uses them in prose.

## 12. Paper Assumption Provenance
No paper-local assumption rows are tracked for this paper; the generated
validator summary above is the current assumption-provenance status. Source
conditions are exposed directly in theorem statements and detailed evidence.

## 13. Displayed Formula Provenance
Displayed and source-defining formulas are tracked through the paper-facing rows in `PaperInterface.lean` and the current statement-match sidecars. This report pass found no standalone formula-provenance issue beyond any source notes already listed above.

## 14. Library Lift Pass
No additional reusable library extraction was needed in this report pass.

## 15. DAG Audit
The dependency DAG was rerendered as `DependencyDAG.pdf` on 2026-06-28.
Visual inspection after rerendering checked for stale open-box notation,
overlap, and missing theorem labels. The DAG shows the GJ19 theorem surface as
formalized and distinguishes theorem nodes from reusable proof-interface nodes.

## 16. Validation Checks

<!-- BEGIN GENERATED LLM-AS-JUDGE RESULTS -->
### LLM-as-Judge Results
- Source coverage (`audit/paper_coverage_llm.json`): 27 covered, 1 covered_by_support.
- Statement match (`audit/statement_match_llm.json`): 56 matches.
- Lean-to-TeX translations (`audit/lean_to_tex_llm.json`): 56 row translations generated from Lean statements.
- Assumption provenance: no assumption-match sidecar tracked for this paper.
- Source-record classification (`audit/source_record_match_llm.json`): 2 validated_source_assumption.
- Source-record structural audit (`audit/source_record_audit.json`): 56 review rows, 2 boundary inputs, 0 recursion failures.
- Review-surface audit (`audit/review_surface_llm.json`): passes over 56 review rows.
- Holistic source-first audit (`docs/AGENT_SOURCE_AUDIT.md`): PASS.
- DAG/source/source-json audit (`docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`): PASS.
<!-- END GENERATED LLM-AS-JUDGE RESULTS -->

Validation commands run on 2026-06-28:

```bash
lake build GJ19OptimalBinaryRatingSystems
python3 scripts/sync_paper_status.py --check
python3 scripts/review_dashboard.py --paper GJ19OptimalBinaryRatingSystems --precheck
python3 scripts/audit_repository.py --paper GJ19OptimalBinaryRatingSystems --paper-closeout --include-active --info-limit 0
```

The build, status sync, and dashboard precheck passed. The closeout audit is
used as the repository-level style/provenance check.

## 17. Paper Definitions Checked
No separate generated definitions table was recorded in this report refresh. The paper-facing definition rows are tracked in `PaperInterface.lean` and the statement validator sidecars.

## 18. Named Theorem Statements Checked
No separate generated theorem table was recorded in this report refresh. Named theorem endpoints are tracked in `PaperInterface.lean`, `status.json`, and the statement validator sidecars.

## 19. Paper-Facing Statement Validator Ledger
Current model-validator sidecars are the source of truth for timestamped rows. Model review has 56 matches across 56 rows. Human dashboard review has 0/56 saved entries, with 0 stale rows and 0 human mismatches.
