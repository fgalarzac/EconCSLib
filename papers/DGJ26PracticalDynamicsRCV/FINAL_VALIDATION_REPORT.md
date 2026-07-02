# Final Validation Report: Simpler Than You Think: The Practical Dynamics of Ranked Choice Voting

Updated: 2026-07-02

## 1. Human Verdict
This formalization covers the paper's theoretical ballot-extension,
exhausted-ballot completion, strengthened candidate-removal, and multi-winner
containment claims at the curated source-facing abstraction. No mathematical
or source-record proof boundary remains on the reviewed theorem surface. Human
dashboard sign-off has not yet been recorded.

## 2. Closeout Status
- Completion status: formalized.
- One-sentence recap: The ballot-extension, exhausted-ballot completion, candidate-removal, and multi-winner containment claims are formalized.
- Lean footprint: 20,736 paper-local Lean LOC; `PaperInterface.lean` is 11027 lines; 50 human-review declarations are exposed.
- Audit summary: paper coverage sidecar is not separately recorded; statement LLM-as-judge sidecar is not separately recorded; assumption provenance sidecar has no rows; source-record audit reports 0 boundary inputs and 0 recursion failures; holistic source-first audit PASS; DAG/source-json audit PASS in `docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`.

## 3. Source and Scope
The formalized source version is the Journal of Computational Social Science
2026 paper, with arXiv:2602.14329 recorded as the public PDF source in
`README.md`. The current Lean scope is the theoretical content: Algorithm 1/A
robust ballot extensions, exhausted-ballot completion, Algorithm 3 strengthened
removal, and Algorithm 4 multi-winner containment.

Empirical election audit findings remain data/code scope outside the theorem
ledger.

## 4. Researcher Summary of Checked Results
- Proposition 1 is formalized: Lean proves that the paper's ballot-extension
  transformations preserve the active support counts needed by the Algorithm A
  strategy analysis.
- Proposition 2 is formalized: Lean proves the exhausted-ballot completion
  equivalence, viable-candidate formulas, and the count-test characterization
  used by the paper.
- Theorem 2.1 is formalized: Lean checks the strengthened candidate-removal
  route, including the one-survival branch and the stated quartic-runtime
  implementation theorem.
- Theorem 2.2 is formalized: Lean checks the Algorithm 4 pairwise condition and
  the resulting multi-winner containment theorem with its quadratic
  verification bound.

## 5. Remaining Boundaries and Gaps
None.

## 6. Additional Assumptions Beyond Paper
No paper-local assumptions are declared in `Assumptions.lean`.

## 7. Proof-Strategy Deviations
None.

## 8. Proof Tricks Worth Reusing
- Reuse ballot suffix/prefix and first-active lemmas for RCV robustness papers.
- Keep Algorithm A support-count closeouts downstream of DGJ24 exact-fill and
  support-count data.
- For conditional algorithmic theorems, expose the paper condition as a formula
  row, then make the reviewed theorem consume that condition directly.

## 9. Mathematical Typos or Other Fixes Suggested in the Source Paper
None found.

## 10. Paper Issues or Caveats
No source-quality issue or theorem caveat is recorded. Human dashboard
sign-off remains pending, and empirical case-study findings are data/code scope
outside the Lean theorem ledger.

## 11. Detailed Formalization Evidence
- `PaperInterface.lean` exposes 50 curated paper-facing review rows and 248
  auxiliary proof-facing rows.
- A targeted source-record audit on the current review surface reports zero
  boundary inputs and zero recursion failures.
- The statement, review-surface, paper-coverage, source-to-Lean, and
  DAG/source-json sidecars and notes are current for the closeout surface.
- `MainTheorems.lean` contains the proof routes for the current seams,
  including Algorithm A support-count data, Algorithm 3 full-run source-branch
  routing, and Algorithm 4 profile-derived source-condition routing.
- Proof organization: DGJ26 remains downstream of DGJ24. Proposition 1 reuses
  DGJ24's checked SmartAllocation support-count route instead of duplicating
  that algorithmic semantics locally. Theorem 2.2 exposes Algorithm 4's source
  pairwise condition as a named paper formula before proving the concrete
  containment endpoint.

## 12. Paper Assumption Provenance
Assumption provenance is tracked in `papers/DGJ26PracticalDynamicsRCV/Assumptions.lean` and `papers/DGJ26PracticalDynamicsRCV/audit/assumption_match_llm.json` when assumption rows exist. No additional assumption-provenance table was separately recorded in this report refresh.

## 13. Displayed Formula Provenance
Displayed and source-defining formulas are tracked through the paper-facing rows in `PaperInterface.lean` and the current statement-match sidecars. This report pass found no standalone formula-provenance issue beyond any source notes already listed above.

## 14. Library Lift Pass
No additional reusable library extraction was needed in this report pass.

## 15. DAG Audit
`DependencyDAG.tex` records the current closeout story as a source-map view:
the visible nodes cover the ballot/support layer, Proposition 1, Proposition 2,
the candidate-removal layer, Theorem 2.1, and Theorem 2.2. The empirical
election-audit content is recorded in this report as data/code scope outside
the Lean theorem ledger rather than as a DAG theorem node. The rendered
`DependencyDAG.pdf` is present and was visually inspected through a PNG
rendering during the closeout pass; it is a nonblank one-page diagram with the
DGJ26 source-result nodes visible and no obvious box, label, or edge overlap.

## 16. Validation Checks
The review dashboard is curated below the oversized-surface threshold. The
paper-coverage audit reports all 44 source inventory items covered directly by
reviewed rows, and the source-record audit reports no boundary inputs or
recursion failures on the 50-row review surface.

### Validation Commands
- `lake build EconCSLib.SocialChoice.Voting.STV`
- `lake env lean papers/DGJ26PracticalDynamicsRCV/PaperInterface.lean`
- `python3 scripts/review_dashboard.py --paper DGJ26PracticalDynamicsRCV --refresh-cache`
- `python3 scripts/review_dashboard.py --paper DGJ26PracticalDynamicsRCV --statement-check`
- `python3 scripts/review_dashboard.py --paper DGJ26PracticalDynamicsRCV --paper-coverage-check`
- `python3 scripts/review_dashboard.py --paper DGJ26PracticalDynamicsRCV --source-to-lean-check`
- `python3 skills/econcs-formalizer/scripts/source_record_audit.py --paper DGJ26PracticalDynamicsRCV --root . --out papers/DGJ26PracticalDynamicsRCV/source_record_audit.json --max-lean-output-chars 30000`
- `python3 scripts/audit_repository.py --paper DGJ26PracticalDynamicsRCV --paper-closeout --include-active --info-limit 0`

## 17. Paper Definitions Checked
No separate generated definitions table was recorded in this report refresh. The paper-facing definition rows are tracked in `PaperInterface.lean` and the statement validator sidecars.

## 18. Named Theorem Statements Checked
No separate generated theorem table was recorded in this report refresh. Named theorem endpoints are tracked in `PaperInterface.lean`, `status.json`, and the statement validator sidecars.

## 19. Paper-Facing Statement Validator Ledger
Current model-validator sidecars are the source of truth for timestamped rows. Model review has none recorded across 0 rows. Human dashboard review has 0/50 saved entries, with 0 stale rows and 0 human mismatches.
