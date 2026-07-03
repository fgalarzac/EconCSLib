# Final Validation Report: Optimal Strategies in Ranked-Choice Voting

Updated: 2026-07-03

## 1. Human Verdict
This formalization covers the paper's mathematical model, algorithmic
reductions, and named theoretical results at the curated source-facing
abstraction. No source-record boundary input remains on the reviewed theorem
surface. Human dashboard sign-off has not yet been recorded.

## 2. Closeout Status
- Completion status: formalized.
- One-sentence recap: The STV/RCV model, SmartAllocation reductions, and Section 5 strategic-voting results are covered at the curated source-facing abstraction.
- Lean footprint: 54,410 paper-local Lean LOC; `PaperInterface.lean` is 32470 lines; 65 human-review declarations are exposed.
- Audit summary: source coverage has 67 covered, 2 conditional_boundary; statement LLM-as-judge has 73 matches, 9 mismatch; resolutions: 9 conditional_boundary; Lean-to-TeX has 82 row translations; assumption provenance sidecar has no rows; source-record classification has 20 approved_external_boundary; source-record audit reports 65 review rows, 0 boundary inputs, 0 recursion failures; review-surface audit passes over 65 review rows; holistic source-first audit PASS; DAG/source-json audit PASS in `docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`.

## 3. Source and Scope
The formalized source version is arXiv:2407.13661, recorded in `README.md`.
The current scope is the theoretical definitions, algorithms, and named claims
around STV/RCV structures, SmartAllocation, irrelevant-candidate and sequence
reductions, and Section 5 strategic-voting statements.

The source-record audit and broader statement/review/dashboard sidecars have
been refreshed for the current curated closeout surface.

## 4. Researcher Summary of Checked Results
- The Appendix B/STV structure layer is formalized: the tie-broken structure
  partition, well-defined STV social choice order, and round-winner/final-loser
  relation are all represented in the review surface.
- The Section 3 algorithmic results are formalized: SmartAllocation optimality
  and runtime, irrelevant-candidate removal, feasible-sequence counting, and
  Algorithm 7 sequence-space reduction are covered by source-facing rows.
- The Section 5 strategic-voting results are formalized: the benefit
  definition, perfect-information coalition impossibility, Case-(A) strategy
  characterization, uncertainty/ex-ante coalition result, and selfish-strategy
  robustness result are all covered.
- The review surface deliberately summarizes implementation routes at the
  paper-result level; detailed proof-route evidence appears in the audit
  ledgers and Lean files listed below.

## 5. Remaining Boundaries and Gaps
None.

## 6. Additional Assumptions Beyond Paper
None.

## 7. Proof-Strategy Deviations
None.

## 8. Proof Tricks Worth Reusing
- Keep shared ballot, STV trace, and active-support lemmas in
  `EconCSLib.SocialChoice.Voting`.
- Split algorithm closeout into formula rows, executable/source-loop rows,
  output-spec constructors, and runtime packaging.
- Audit record and certificate fields recursively before marking a paper row
  fully formalized.

## 9. Mathematical Typos or Other Fixes Suggested in the Source Paper
None found.

## 10. Paper Issues or Caveats
No source-quality issue or theorem caveat is recorded. The two helper-formula
conditional coverage annotations described above are source-inventory scope
notes, not suspected paper mistakes. Human dashboard sign-off has not yet been
recorded.

## 11. Detailed Formalization Evidence
- `PaperInterface.lean` exposes 65 curated paper-facing review rows and 422
  auxiliary proof-facing rows.
- A targeted source-record audit on the current review surface reports no
  recursion failures and zero boundary inputs.
- `MainTheorems.lean` and `SmartAllocationSource.lean` contain the checked
  implementation route for the current theorem seams, including the Algorithm 6
  source-condition route, the Algorithm 7 sorted-transfer constructed
  generated-winner route with internally derived initial losing-label
  prefix, the auxiliary canonical replay-equality route, the canonical
  source-run-check constructor from generated-round constraints, the
  canonical-profile source-check and source-facts specializations, the
  generated-trace initial-loss-prefix bridge, the canonical Predict-Losses
  profile prefix helper, the auxiliary combined canonical Algorithm 7 checker
  bridge, the Algorithm 3 candidate-allocation/voter-block routes plus finite
  checker as auxiliary endpoints, and the canonical Predict-Losses
  generated-trace source-loop bridge.

- Source-faithful interface note: the current interface exposes source-level
  parameters and conditional theorem hypotheses where the paper statements
  themselves are conditional. This is part of the source-faithful theorem
  surface, not a proof-strategy deviation.

## 12. Paper Assumption Provenance
No paper-local assumption rows are tracked for this paper; the generated
validator summary above is the current assumption-provenance status. Source
parameters and conditional theorem hypotheses are exposed directly in the
paper-facing statements and detailed evidence.

## 13. Displayed Formula Provenance
Displayed and source-defining formulas are tracked through the paper-facing rows in `PaperInterface.lean` and the current statement-match sidecars. This report pass found no standalone formula-provenance issue beyond any source notes already listed above.

## 14. Library Lift Pass
No additional reusable library extraction was needed in this report pass.

## 15. DAG Audit
`DependencyDAG.tex` records the current closeout story as a source-map view:
the visible nodes cover the model/structure layer, Algorithms 1--7,
Proposition 2.1, Theorem B.1, Lemma B.2, Proposition 3.3, Theorems 3.1 and
3.2, Proposition 3.4, Definition 5.1, Propositions 5.3, 5.5, and 5.6, and
Theorem 5.4. The rendered `DependencyDAG.pdf` is present and was visually
inspected through a PNG rendering during the closeout pass; it is a nonblank
one-page diagram with the DGJ24 source-result nodes visible and no obvious box,
label, or edge overlap.

## 16. Validation Checks

<!-- BEGIN GENERATED LLM-AS-JUDGE RESULTS -->
### LLM-as-Judge Results
- Source coverage (`paper_coverage_llm.json`): 67 covered, 2 conditional_boundary.
- Statement match (`statement_match_llm.json`): 73 matches, 9 mismatch; resolutions: 9 conditional_boundary.
- Lean-to-TeX translations (`lean_to_tex_llm.json`): 82 row translations generated from Lean statements.
- Assumption provenance (`assumption_match_llm.json`): no rows.
- Source-record classification (`source_record_match_llm.json`): 20 approved_external_boundary.
- Source-record structural audit (`source_record_audit.json`): 65 review rows, 0 boundary inputs, 0 recursion failures.
- Review-surface audit (`review_surface_llm.json`): passes over 65 review rows.
- Holistic source-first audit (`docs/AGENT_SOURCE_AUDIT.md`): PASS.
- DAG/source/source-json audit (`docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`): PASS.
<!-- END GENERATED LLM-AS-JUDGE RESULTS -->

The review dashboard is curated below the oversized-surface threshold. The
statement, review-surface, paper-coverage, source-to-Lean, and source-record
sidecars are current for the closeout surface.

### Validation Commands
- `lake build EconCSLib.SocialChoice.Voting.STV`
- `lake env lean papers/DGJ24OptimalStrategiesRCV/PaperInterface.lean`
- `python3 scripts/review_dashboard.py --paper DGJ24OptimalStrategiesRCV --refresh-cache`
- `python3 scripts/review_dashboard.py --paper DGJ24OptimalStrategiesRCV --statement-check`
- `python3 scripts/review_dashboard.py --paper DGJ24OptimalStrategiesRCV --paper-coverage-check`
- `python3 scripts/review_dashboard.py --paper DGJ24OptimalStrategiesRCV --source-to-lean-check`
- `python3 skills/econcs-formalizer/scripts/source_record_audit.py --paper DGJ24OptimalStrategiesRCV --out papers/DGJ24OptimalStrategiesRCV/source_record_audit.json`
- `python3 scripts/audit_repository.py --paper DGJ24OptimalStrategiesRCV --paper-closeout --include-active --info-limit 0`

## 17. Paper Definitions Checked
No separate generated definitions table was recorded in this report refresh. The paper-facing definition rows are tracked in `PaperInterface.lean` and the statement validator sidecars.

## 18. Named Theorem Statements Checked
No separate generated theorem table was recorded in this report refresh. Named theorem endpoints are tracked in `PaperInterface.lean`, `status.json`, and the statement validator sidecars.

## 19. Paper-Facing Statement Validator Ledger
Current source: `statement_match_llm.json`, refreshed 2026-07-02, plus assumption provenance in `assumption_match_llm.json`.

| Validator surface | Result |
| --- | --- |
| Statement match | 73 matches, 9 mismatch; resolutions: 9 conditional_boundary. |
| Lean-to-TeX drafts | 82 row translations generated from Lean statements. |
| Assumption provenance | no rows. |
| Source coverage | 67 covered, 2 conditional_boundary. |

The full row-level validator ledger is tracked in the JSON sidecars. Human
dashboard reviews and model/agent statement checks are separate provenance lanes;
this report does not change the human-only `human_review.reviewed_rows` counter.
