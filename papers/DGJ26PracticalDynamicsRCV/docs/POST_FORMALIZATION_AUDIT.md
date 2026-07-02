# Post-Formalization Audit: Simpler Than You Think: The Practical Dynamics of Ranked Choice Voting

## Scope

This file records the DGJ26 closeout state after the reviewed theorem surface
was retargeted away from superseded component/checker endpoints and toward
source-facing Algorithm A, Algorithm 3, and Algorithm 4 endpoints.

Current status: formalized. Human dashboard sign-off has not yet been
recorded; that is a review-process item, not a theorem caveat.

Lean footprint: 20,736 paper-local Lean lines across 3 files, including 11,027
lines in `PaperInterface.lean`.

The researcher-facing closeout narrative is `FINAL_VALIDATION_REPORT.md`.

## DAG Audit

`DependencyDAG.tex` has been updated to reflect the current closeout story:
Proposition 1, Proposition 2, Theorem 2.1, and Theorem 2.2 are formalized
result nodes. Empirical election-audit content is recorded as data/code scope
in the final report rather than as a theorem node. `DependencyDAG.pdf` is
present, one page, and was rendered to a PNG for visual inspection during
closeout. The rendered diagram was nonblank, with visible DGJ26 nodes and no
obvious label, box, or edge overlap.

## Validation Commands

Lean targets:

```bash
lake build EconCSLib.SocialChoice.Voting.STV
lake env lean papers/DGJ26PracticalDynamicsRCV/PaperInterface.lean
```

Dashboard and source-record checks:

```bash
python3 scripts/review_dashboard.py --paper DGJ26PracticalDynamicsRCV --refresh-cache
python3 scripts/review_dashboard.py --paper DGJ26PracticalDynamicsRCV --statement-check
python3 scripts/review_dashboard.py --paper DGJ26PracticalDynamicsRCV --paper-coverage-check
python3 scripts/review_dashboard.py --paper DGJ26PracticalDynamicsRCV --source-to-lean-check
python3 skills/econcs-formalizer/scripts/source_record_audit.py --paper DGJ26PracticalDynamicsRCV --root . --out papers/DGJ26PracticalDynamicsRCV/source_record_audit.json --max-lean-output-chars 30000
```

Completed-paper repository audit:

```bash
python3 scripts/audit_repository.py --paper DGJ26PracticalDynamicsRCV --paper-closeout --include-active --info-limit 0
```

## Source-First Audit

`docs/AGENT_SOURCE_AUDIT.md` records the independent source-first comparison of the
cached source text, the curated Lean review surface, and the machine audit
evidence.

## Residual Notes

No source-record boundary input remains on the 50-row review surface. Empirical
case-study findings are outside Lean theorem scope. Human dashboard sign-off
has not yet been recorded.

## Separate Holistic DAG--Source JSON Pass

This pass is separate from the source-record, statement-match, and
source-to-Lean checks above. I compared the cached source text, the curated
44-item `paper_statement_map.json` inventory, `paper_coverage_llm.json`, and
the current `DependencyDAG.tex`.

The DAG is intentionally less granular than the 50-row Lean review surface, but
every named source-result cluster in the inventory is visible as a DAG node or
an explicitly named grouped node: the ballot/support layer for Algorithm 1/A
and Proposition 1, the exhausted-ballot and viable-set layer for Proposition 2,
the candidate-removal layer for Definition B.1 and Algorithms 2--3, Theorem
2.1, and the Algorithm 4/Theorem 2.2 multi-winner containment route. Empirical
election-audit content is data/code scope rather than a theorem-ledger node.

Conclusion: PASS. The DAG matches the source coverage ledger at the
source-result-cluster level. It does not attempt to draw every formula row or
auxiliary Lean declaration, but it captures the paper's reviewed mathematical
and algorithmic theorem clusters.
