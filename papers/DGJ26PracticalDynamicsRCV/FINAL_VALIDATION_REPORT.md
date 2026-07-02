# Final Validation Report: Simpler Than You Think: The Practical Dynamics of Ranked Choice Voting

## 1. Human Verdict

This formalization covers the paper's theoretical ballot-extension,
exhausted-ballot completion, strengthened candidate-removal, and multi-winner
containment claims at the curated source-facing abstraction. No mathematical
or source-record proof boundary remains on the reviewed theorem surface. Human
dashboard sign-off has not yet been recorded.

## 2. Closeout Status

- Completion status: formalized
- Paper-facing review rows: 50
- Auxiliary proof-facing rows: 248
- Lean footprint: 20,736 paper-local Lean lines across 3 files, including
  11,027 lines in `PaperInterface.lean`.
- Main Lean target: `lake build EconCSLib.SocialChoice.Voting.STV` followed by
  `lake env lean papers/DGJ26PracticalDynamicsRCV/PaperInterface.lean`
- Source coverage and source-to-Lean: 44/44 source statements are covered
  directly, with 0 missing, stale, or flagged items.
- LLM-as-judge statement lane: 50 current review rows, 69 Lean-to-TeX drafts,
  and 69 statement-judge rows, with 0 missing, stale, or flagged items.
- Source-record provenance: 50/50 configured review rows, 0 boundary inputs,
  and 0 recursion failures.
- Holistic source-first and DAG/source-json audits: PASS. The independent
  source audit found no omitted source theorem, hidden strengthening, hidden
  weakening, or semantic mismatch; the separate DAG/source-json pass confirms
  the DAG matches the source coverage ledger at the source-result-cluster
  level.

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

## 9. Paper Issues or Caveats

No source-quality issue or theorem caveat is recorded. Human dashboard
sign-off remains pending, and empirical case-study findings are data/code scope
outside the Lean theorem ledger.

## 10. Detailed Formalization Evidence

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

## 11. Review Surface Audit

The review dashboard is curated below the oversized-surface threshold. The
paper-coverage audit reports all 44 source inventory items covered directly by
reviewed rows, and the source-record audit reports no boundary inputs or
recursion failures on the 50-row review surface.

## 12. Validation Commands

- `lake build EconCSLib.SocialChoice.Voting.STV`
- `lake env lean papers/DGJ26PracticalDynamicsRCV/PaperInterface.lean`
- `python3 scripts/review_dashboard.py --paper DGJ26PracticalDynamicsRCV --refresh-cache`
- `python3 scripts/review_dashboard.py --paper DGJ26PracticalDynamicsRCV --statement-check`
- `python3 scripts/review_dashboard.py --paper DGJ26PracticalDynamicsRCV --paper-coverage-check`
- `python3 scripts/review_dashboard.py --paper DGJ26PracticalDynamicsRCV --source-to-lean-check`
- `python3 skills/econcs-formalizer/scripts/source_record_audit.py --paper DGJ26PracticalDynamicsRCV --root . --out papers/DGJ26PracticalDynamicsRCV/source_record_audit.json --max-lean-output-chars 30000`
- `python3 scripts/audit_repository.py --paper DGJ26PracticalDynamicsRCV --paper-closeout --include-active --info-limit 0`

## 13. DAG Audit

`DependencyDAG.tex` records the current closeout story as a source-map view:
the visible nodes cover the ballot/support layer, Proposition 1, Proposition 2,
the candidate-removal layer, Theorem 2.1, and Theorem 2.2. The empirical
election-audit content is recorded in this report as data/code scope outside
the Lean theorem ledger rather than as a DAG theorem node. The rendered
`DependencyDAG.pdf` is present and was visually inspected through a PNG
rendering during the closeout pass; it is a nonblank one-page diagram with the
DGJ26 source-result nodes visible and no obvious box, label, or edge overlap.
