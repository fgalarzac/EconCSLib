# Post-Formalization Audit: Optimal Strategies in Ranked-Choice Voting

## Scope

This file records the DGJ24 closeout state after the reviewed theorem surface
was retargeted away from finite checker endpoints and toward source-facing
Algorithm 3, Algorithm 6, Algorithm 7, and Section 5 endpoints.

Current status: formalized. Human dashboard sign-off has not yet been
recorded; that is a review-process item, not a theorem caveat.

The researcher-facing closeout narrative is `FINAL_VALIDATION_REPORT.md`.

## DAG Audit

`DependencyDAG.tex` has been updated to reflect the current closeout story as
a source-map view, not a helper-family changelog. It now exposes the
model/structure layer, Algorithms 1--7, Proposition 2.1, Theorem B.1, Lemma
B.2, Proposition 3.3, Theorems 3.1 and 3.2, Proposition 3.4, Definition 5.1,
Propositions 5.3, 5.5, and 5.6, and Theorem 5.4. `DependencyDAG.pdf` is
present, one page, and was rendered to a PNG for visual inspection during
closeout. The rendered diagram was nonblank, with visible DGJ24 source-result
nodes and no obvious label, box, or edge overlap.

## Validation Commands

Lean targets:

```bash
lake build EconCSLib.SocialChoice.Voting.STV
lake env lean papers/DGJ24OptimalStrategiesRCV/PaperInterface.lean
```

Dashboard and source-record checks:

```bash
python3 scripts/review_dashboard.py --paper DGJ24OptimalStrategiesRCV --refresh-cache
python3 scripts/review_dashboard.py --paper DGJ24OptimalStrategiesRCV --statement-check
python3 scripts/review_dashboard.py --paper DGJ24OptimalStrategiesRCV --paper-coverage-check
python3 scripts/review_dashboard.py --paper DGJ24OptimalStrategiesRCV --source-to-lean-check
python3 skills/econcs-formalizer/scripts/source_record_audit.py --paper DGJ24OptimalStrategiesRCV --root . --out papers/DGJ24OptimalStrategiesRCV/source_record_audit.json --max-lean-output-chars 30000
```

Completed-paper repository audit:

```bash
python3 scripts/audit_repository.py --paper DGJ24OptimalStrategiesRCV --paper-closeout --include-active --info-limit 0
```

## Source-First Audit

`AGENT_SOURCE_AUDIT.md` records the independent source-first comparison of the
cached arXiv source text, the curated Lean review surface, and the machine
audit evidence.

## Residual Notes

No source-record boundary input remains on the 65-row review surface. The two
conditional paper-coverage helper rows are Algorithm 7 source-parameter formula
rows, not standalone theorem gaps. Human dashboard sign-off has not yet been
recorded.

## Separate Holistic DAG--Source JSON Pass

This pass is separate from the source-record, statement-match, and
source-to-Lean checks above. I compared the cached source text, the curated
`paper_statement_map.json` inventory, `paper_coverage_llm.json`, and the
current `DependencyDAG.tex`.

The source JSON inventory has 69 items. The DAG is intentionally less granular
than the 65-row Lean review surface, but every named source-result cluster in
the inventory is now visible as a DAG node or an explicitly named grouped node:
the RCV/STV model and structure constraints; Algorithms 1--2 and Proposition
2.1; Theorem B.1 and Lemma B.2; Algorithm 3 and Theorem 3.1; Algorithms 4--6,
Lemma C.1, and Theorem 3.2; Proposition 3.3; Algorithm 7 and Proposition 3.4;
Definition 5.1; Propositions 5.3, 5.5, and 5.6; and Theorem 5.4.

Conclusion: PASS. The DAG now matches the source coverage ledger at the
source-result-cluster level. It does not attempt to draw every formula row or
auxiliary Lean declaration, but it no longer collapses the Section 3 algorithm
results and Section 5 strategic results into a single generic strategy node.
