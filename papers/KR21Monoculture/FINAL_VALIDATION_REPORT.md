# Final Validation Report: KR21 Monoculture

Updated: 2026-07-03

## 1. Human Verdict
Formalized. The main Mallows and three-candidate Gaussian/Laplace RUM routes are formalized. No named theorem or main-text result is affected by the Appendix C Lemma 1 source note recorded below.
No human dashboard sign-off has been recorded.

## 2. Closeout Status
- Completion status: formalized.
- One-sentence recap: The algorithmic-monoculture welfare results are formalized with finite and continuous score-space conditions made explicit.
- Lean footprint: 65,666 paper-local Lean LOC; `PaperInterface.lean` is a 17-line compact entrypoint; `AuditInterface.lean` is 1,819 lines and contains the 49 configured dashboard/LLM-as-judge declarations.
- Audit summary: source coverage has 49 covered; statement LLM-as-judge has 49 matches; Lean-to-TeX has 49 row translations; assumption provenance sidecar is not tracked; source-record classification has 1 validated_source_assumption, 6 nonpropositional_witness_data; source-record audit reports 49 review rows, 1 boundary input, 0 recursion failures; review-surface audit passes over 49 review rows; holistic source-first audit PASS; DAG/source-json audit PASS in `docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`.

## 3. Source and Scope
- Paper: *Algorithmic Monoculture and Social Welfare*.
- Authors: Jon Kleinberg and Manish Raghavan.
- Source version: arXiv:2101.05853 / PNAS 2021.
- Local source cache: `papers/KR21Monoculture/sources/`.
- Lean folder: `papers/KR21Monoculture`.
- Human-facing theorem file: `papers/KR21Monoculture/PaperInterface.lean`.
- Row-level audit surface: `papers/KR21Monoculture/AuditInterface.lean`.
- Machine-readable status: `papers/KR21Monoculture/status.json`.
- DAG artifacts: `papers/KR21Monoculture/docs/DependencyDAG.tex`, `papers/KR21Monoculture/docs/DependencyDAG.pdf`.

## 4. Researcher Summary of Checked Results
- Theorem 1 is formalized in the paper's conditional family form and in the concrete Mallows family form.
- Theorem 2 is formalized for the three-candidate Gaussian route and for Laplace routes, including source-model variants that derive Definition 2, Definition 3, removal monotonicity, and high-accuracy concentration ingredients.
- Theorem 3 is formalized for Mallows laws with common center and stricter algorithmic accuracy; the rank-factorization formulas are proved rather than assumed.
- Theorem 4 is formalized for weak all-human optimality and strict unique human optimality at every nonterminal history.
- Appendix A scaled-noise monotonicity and concentration consequences are formalized for the finite/measure source surfaces used by the paper-facing RUM routes.
- Appendix C Theorems 6, 7, and 8 are covered through the three-candidate Gaussian/Laplace source routes; the Laplacian Lemma 1 source note below does not affect any named theorem or main-text result.
- Appendix E/D Mallows family results are formalized through the concrete Mallows family assumption package and Theorem 9 route.

## 5. Remaining Boundaries and Gaps
No proof boundary remains for the paper-facing status.

## 6. Additional Assumptions Beyond Paper
None.

## 7. Proof-Strategy Deviations
- Source route: Appendix C states a global strict Laplacian well-ordering
  claim. Lean route: the formalization uses the mathematically valid weak form
  and obtains strict downstream conclusions from the later support and
  monotonicity arguments. This matters because the global strict pointwise claim
  is false, while the named downstream theorems remain formalized.
- Source route: the Mallows sequential-optimality proof relies on broad
  monotonicity intuition. Lean route: the proof isolates a reduced same-size
  prefix-cut weighted-extremes cancellation theorem, proves first-choice
  prefix-cut probability comparisons, deletes absent extremes and trivial cuts,
  and routes Theorem 4 through remaining-utility dominance. This avoids
  assuming an unproved broad weak-Bruhat/Mallows monotonicity theorem.

## 8. Proof Tricks Worth Reusing
- For source claims that contain a false strict lemma but a true downstream theorem, prove a corrected lemma and then prove the downstream theorem from exactly the weaker lemma plus the later strictness source.
- For Mallows comparisons, derive first-choice and prefix inequalities from rank-factorization lemmas and route the sequential theorem through remaining-utility dominance.
- For RUM contraction arguments, separate deterministic contraction monotonicity, no-tie measurability, full-support strict regions, and atomwise concentration into reusable endpoints before assembling Theorem 2.

## 9. Mathematical Typos or Other Fixes Suggested in the Source Paper
None found.

## 10. Paper Issues or Caveats
No paper-level caveat is recorded.

Audit note for Appendix C Lemma 1: the paper states a global strict Laplacian well-ordering claim. Lean proves the globally valid weak Laplacian inequality and strict overlap/local forms. The downstream Laplace theorem is proved from that weak comparison plus the separate strict support/monotonicity ingredients used later in the paper. The short note `LAPLACIAN_LEMMA1_SOURCE_NOTE.md` records the paper statement, the Lean-proved statement, and a concrete counterexample to the global strict Laplacian statement.

No named theorem or main-text result is affected by this source-note correction. It is not an added assumption and not an external proof boundary.

## 11. Detailed Formalization Evidence
`AuditInterface.lean` exposes 49 reviewed paper-facing rows and 16 auxiliary helper rows. The reviewed surface includes:

- paper definitions and source predicates: Mallows specification, well-ordered noise, Definition 1 continuity/asymptotic behavior;
- Appendix A finite and measure contraction monotonicity, strict full-support consequences, no-tie/measurability, and atomwise concentration;
- Appendix C Gaussian strict well-ordering, Laplacian weak well-ordering, Theorem 6 weaker-competition routes, Theorem 7 Laplace derivative cases, and Definition 2 independent-reranking routes;
- Theorem 2 Gaussian and Laplace source routes;
- Theorem 1 conditional and concrete Mallows forms;
- Theorem 3 Mallows paper-hypotheses route;
- Theorem 4 weak and strict sequential optimality routes.

The auxiliary rows are proof-route artifacts such as explicit concentration/limit boundary helpers, negative-correlation certificates, and Laplacian lambda-certificate variants. They are not used as hidden paper-status boundaries.

Several source-facing endpoints expose finite and continuous score-space
conditions explicitly rather than hiding them behind proof certificates.
Certificate and boundary helper rows are classified as auxiliary in
`status.json`.
Visible hypotheses such as positive accuracy, strict value ordering, nonempty
remaining sets, density normalization, full-support/no-tie conditions, and
Mallows parameter inequalities are source theorem conditions or model
parameters.

## 12. Paper Assumption Provenance
No KR21-specific `Assumptions.lean` ledger is used for the final status. The paper-facing reviewed rows have no additional non-source assumptions recorded in `status.json`.

The conditional Theorem 1 row takes the paper's Definitions 1--3 package as its visible theorem condition. Concrete Mallows and concrete RUM source routes construct the relevant packages rather than treating them as external proof debt.

## 13. Displayed Formula Provenance
Displayed and source-defining formulas are tracked through the paper-facing rows in `AuditInterface.lean` and the current statement-match sidecars. This report pass found no standalone formula-provenance issue beyond any source notes already listed above.

## 14. Library Lift Pass
Reusable ranking-payoff, Mallows, finite-expectation, conditional-probability, no-tie, and RUM contraction infrastructure now lives in shared `EconCSLib` modules where it is useful beyond KR21. KR21 paper-local files keep paper-shaped wrappers where theorem numbering and source-note clarity matter.

## 15. DAG Audit
`DependencyDAG.tex` uses the shared TikZ preamble and is paper-facing: node labels state paper definitions, lemmas, and theorems rather than Lean declaration names. `DependencyDAG.pdf` was rendered from the paper folder with `latexmk -pdf -interaction=nonstopmode -halt-on-error DependencyDAG.tex`, converted to a PNG for visual inspection, and checked for node/text overlap and stale open-boundary labels. The DAG shows the paper-facing result flow as formalized; the Laplacian Lemma 1 strict-vs-weak distinction is documented as an audit note rather than a theorem-status caveat.

## 16. Validation Checks

<!-- BEGIN GENERATED LLM-AS-JUDGE RESULTS -->
### LLM-as-Judge Results
- Source coverage (`paper_coverage_llm.json`): 49 covered.
- Statement match (`statement_match_llm.json`): 49 matches.
- Lean-to-TeX translations (`lean_to_tex_llm.json`): 49 row translations generated from Lean statements.
- Assumption provenance: no assumption-match sidecar tracked for this paper.
- Source-record classification (`source_record_match_llm.json`): 1 validated_source_assumption, 6 nonpropositional_witness_data.
- Source-record structural audit (`source_record_audit.json`): 49 review rows, 1 boundary input, 0 recursion failures.
- Review-surface audit (`review_surface_llm.json`): passes over 49 review rows.
- Holistic source-first audit (`docs/AGENT_SOURCE_AUDIT.md`): PASS.
- DAG/source/source-json audit (`docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`): PASS.
<!-- END GENERATED LLM-AS-JUDGE RESULTS -->

Passed during this closeout pass:

```bash
lake build KR21Monoculture.PaperInterface
python3 scripts/review_dashboard.py --paper KR21Monoculture --precheck
python3 scripts/review_dashboard.py --paper KR21Monoculture --source-to-lean-precheck
```

Targeted closeout command for the final audit:

```bash
python3 scripts/audit_repository.py --paper KR21Monoculture --paper-closeout --include-active --info-limit 0
```

The final closeout audit is rerun after every KR21 report, status, sidecar, or DAG edit until it reports no KR21-specific errors or warnings.

## 17. Paper Definitions Checked
No separate generated definitions table was recorded in this report refresh. The paper-facing definition rows are tracked in `AuditInterface.lean` and the statement validator sidecars.

## 18. Named Theorem Statements Checked
No separate generated theorem table was recorded in this report refresh. Named theorem endpoints are tracked in `AuditInterface.lean`, `status.json`, and the statement validator sidecars.

## 19. Paper-Facing Statement Validator Ledger
The current dashboard sidecars are regenerated as part of closeout:

- `lean_to_tex_llm.json`
- `statement_match_llm.json`
- `paper_statement_map.json`
- `paper_coverage_llm.json`
- `source_record_audit.json`
- `source_record_match_llm.json`

Human dashboard reviews have not been saved yet, so `human_review.reviewed_rows` remains zero. The model/agent statement checks are audit evidence for source alignment; the Lean builds and axiom audit are the proof evidence.
