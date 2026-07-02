# Final Validation Report: Optimal Strategies in Ranked-Choice Voting

## 1. Human Verdict

This formalization covers the paper's mathematical model, algorithmic
reductions, and named theoretical results at the curated source-facing
abstraction. No source-record boundary input remains on the reviewed theorem
surface. Human dashboard sign-off has not yet been recorded.

## 2. Closeout Status

- Completion status: formalized
- Paper-facing review rows: 65
- Auxiliary proof-facing rows: 422
- Lean footprint: 54,410 paper-local Lean lines across 4 files, including
  33,535 lines in `PaperInterface.lean`.
- Main Lean target: `lake build EconCSLib.SocialChoice.Voting.STV` followed by
  `lake env lean papers/DGJ24OptimalStrategiesRCV/PaperInterface.lean`
- Source coverage and source-to-Lean: 67/69 source statements are covered
  directly; the remaining 2 are Algorithm 7 source-parameter formula rows
  covered as conditional source parameters, with 0 missing, stale, or flagged
  items.
- LLM-as-judge statement lane: 65 current review rows, 82 Lean-to-TeX drafts,
  and 82 statement-judge rows, with 0 missing, stale, or flagged items.
- Source-record provenance: 65/65 configured review rows, 0 boundary inputs,
  and 0 recursion failures.
- Holistic source-first and DAG/source-json audits: PASS. The independent
  source audit found no omitted source theorem, hidden strengthening, hidden
  weakening, or semantic mismatch; the separate DAG/source-json pass confirms
  the DAG matches the source coverage ledger at the source-result-cluster
  level.

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

No paper-local assumptions are declared in `Assumptions.lean`.

## 7. Proof-Strategy Deviations

None.

Source-faithful interface note: the current interface exposes source-level
parameters and conditional theorem hypotheses where the paper statements
themselves are conditional. This is part of the source-faithful theorem
surface.

## 8. Proof Tricks Worth Reusing

- Keep shared ballot, STV trace, and active-support lemmas in
  `EconCSLib.SocialChoice.Voting`.
- Split algorithm closeout into formula rows, executable/source-loop rows,
  output-spec constructors, and runtime packaging.
- Audit record and certificate fields recursively before marking a paper row
  fully formalized.

## 9. Paper Issues or Caveats

No source-quality issue or theorem caveat is recorded. The two helper-formula
conditional coverage annotations described above are source-inventory scope
notes, not suspected paper mistakes. Human dashboard sign-off has not yet been
recorded.

## 10. Detailed Formalization Evidence

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

## 11. Review Surface Audit

The review dashboard is curated below the oversized-surface threshold. The
statement, review-surface, paper-coverage, source-to-Lean, and source-record
sidecars are current for the closeout surface.

## 12. Validation Commands

- `lake build EconCSLib.SocialChoice.Voting.STV`
- `lake env lean papers/DGJ24OptimalStrategiesRCV/PaperInterface.lean`
- `python3 scripts/review_dashboard.py --paper DGJ24OptimalStrategiesRCV --refresh-cache`
- `python3 scripts/review_dashboard.py --paper DGJ24OptimalStrategiesRCV --statement-check`
- `python3 scripts/review_dashboard.py --paper DGJ24OptimalStrategiesRCV --paper-coverage-check`
- `python3 scripts/review_dashboard.py --paper DGJ24OptimalStrategiesRCV --source-to-lean-check`
- `python3 skills/econcs-formalizer/scripts/source_record_audit.py --paper DGJ24OptimalStrategiesRCV --out papers/DGJ24OptimalStrategiesRCV/source_record_audit.json`
- `python3 scripts/audit_repository.py --paper DGJ24OptimalStrategiesRCV --paper-closeout --include-active --info-limit 0`

## 13. DAG Audit

`DependencyDAG.tex` records the current closeout story as a source-map view:
the visible nodes cover the model/structure layer, Algorithms 1--7,
Proposition 2.1, Theorem B.1, Lemma B.2, Proposition 3.3, Theorems 3.1 and
3.2, Proposition 3.4, Definition 5.1, Propositions 5.3, 5.5, and 5.6, and
Theorem 5.4. The rendered `DependencyDAG.pdf` is present and was visually
inspected through a PNG rendering during the closeout pass; it is a nonblank
one-page diagram with the DGJ24 source-result nodes visible and no obvious box,
label, or edge overlap.
