# Post-Formalization Closeout

Read this file before declaring a paper done, running a
post-validation/post-formalization pass, preparing a public PR closeout, or
editing a paper's final validation report after a completed proof phase. Do not
run this workflow for routine in-progress proof loops unless the user asks for
post-validation.

Keep this as the single closeout reference for now. The final report, audit
sidecars, source-first audit, DAG/source-json comparison, LOC sourcing, and
note/gap/deviation classification are one coherent workflow. If this file later
gets too large, split only DAG-specific visual/layout rules into a separate
`references/dependency-dags.md`.

## Closeout Gate

At closeout, verify the target paper only. Do not rerun all-paper
LLM-as-judge jobs unless the user explicitly asks for an all-paper refresh.

Required target-paper checks:

1. Refresh the uncached dashboard row surface for the target paper.
2. Confirm every `PaperInterface.lean` declaration is classified in
   `status.json` under `review_surface.include_names`,
   `review_surface.assumption_names`, or `review_surface.auxiliary_names`.
3. Build or refresh a source-curated `paper_statement_map.json` from the source
   paper, not from Lean row names. For public-facing statuses, a missing
   explicit source inventory is a closeout blocker.
4. Verify `paper_coverage_llm.json` against current dashboard row names. This
   paper-level source-to-dashboard lane is the only LLM-as-judge lane that says
   whether every source statement is represented.
5. Verify `lean_to_tex_llm.json` for every current non-assumption review row
   using source-stable declaration digests.
6. Verify `statement_match_llm.json` with the strict full-statement,
   exact-formula prompt. The raw row judgment should stay strict:
   intentionally accepted conditional rows remain `mismatch` with
   `resolution: "conditional_boundary"`.
7. Verify `assumption_match_llm.json` for every assumption and proof-boundary
   name. Source-assumption provenance must work at premise granularity through
   `premise_judgments`.
8. Generate or refresh the code-backed recursive source-record audit for every
   row whose statement or visible premises mention a record, certificate,
   replay, process, bridge, source model, source row, or consequence package.
   Save `source_record_audit.json` and refresh `source_record_match_llm.json`
   only for missing, stale, or structurally changed target-paper rows.
9. Inspect source-record classifications before setting status. Remaining
   `approved_external_boundary`, `unresolved_assumed_math`, stale
   source-record digests, or missing source-record judgments make the affected
   row partial/conditional unless Lean has discharged the field or the status
   claim explicitly excludes that source item.
10. Run a proof-level library-lift pass. Extract small, targeted generic
    lemmas/results when the destination is clear and the relevant builds can be
    checked; otherwise record the candidate and destination module in the final
    report.
11. Run a skill-update pass. If the paper taught a reusable workflow lesson,
    update this skill or an appropriate reference before final handoff; if it
    did not, state that explicitly in the final report or handoff.
12. Update `docs/DependencyDAG.tex`, render `docs/DependencyDAG.pdf`, visually inspect
    it, and record the DAG evidence in the final report and post-formalization
    audit note.
13. Write or refresh `docs/AGENT_SOURCE_AUDIT.md` as an independent source-first
    holistic audit. It must read the source first, build or verify the source
    inventory from the source itself, then inspect `PaperInterface.lean` and
    Lean statements for omissions, hidden strengthening/weakening, and semantic
    mismatches. It must not merely summarize existing sidecars. Write
    `## Overall status: PASS` only when the independent source-first audit
    agrees that the claimed source surface is covered.
14. Run the targeted repository closeout audit after report/DAG edits:
    `python3 scripts/audit_repository.py --paper <paper-folder> --paper-closeout --include-active --info-limit 0`.
    Do not claim post-formalization completion while it reports missing/stale
    DAG, validation-report, source-record, LLM-sidecar, or hidden-premise
    findings for that paper.
15. Rerun `python3 scripts/review_dashboard.py --paper <paper-folder> --precheck`
    and record all remaining unresolved `mismatch`, accepted
    `conditional_boundary`, `uncertain`, stale, missing, or broad-surface
    findings in the final report.
16. Update paper-local `status.json` at the same time as the DAG and final
    report, then run `python3 scripts/sync_paper_status.py` so generated
    status tables move with the paper-local source of truth.
    The root `README.md` is protected hand-written prose and must not be edited
    during closeout unless the user gives specific root-README instructions.
17. Refresh the final-report LLM-as-judge summary block from the sidecars.
    In the public repository, run
    `python3 scripts/refresh_validation_report_audit_summaries.py` and then
    `python3 scripts/refresh_validation_report_audit_summaries.py --check`.
    Do not hand-write that source coverage, statement-match, Lean-to-TeX,
    assumption-provenance, source-record, review-surface, holistic, or DAG
    result text; if a sidecar exists, the report must not say it is "not
    separately recorded".

The full closeout gate is for completed papers, intentionally approved
conditional closeouts, public PR preparation, or explicit user-requested
post-validation. For unfinished active papers, use targeted Lean builds,
placeholder scans, JSON sanity checks, and row-scoped audit refreshes only for
changed rows.

## Final Validation Report

`FINAL_VALIDATION_REPORT.md` is a concise human assessment, not a handoff note,
implementation ledger, or shell transcript. It must put an `Updated: YYYY-MM-DD`
line directly below the H1 title, using the date of the report's latest
substantive refresh. It must answer four questions near the top:

- What was proved?
- Did formalization find anything wrong or ambiguous in the paper?
- Was any qualitatively different proof/modeling route needed?
- What remains for Lean proof work versus human dashboard review?

Write in paper language, not Lean-internal implementation language. Avoid
history markers such as `previously`, `now`, `restored`, or `superseded`
unless the historical comparison is itself a source-paper caveat or requested
retrospective.

Use this section order:

1. Human Verdict
2. Closeout Status
3. Source and Scope
4. Researcher Summary of Checked Results
5. Remaining Boundaries and Gaps
6. Additional Assumptions Beyond Paper
7. Proof-Strategy Deviations
8. Proof Tricks Worth Reusing
9. Mathematical Typos or Other Fixes Suggested in the Source Paper
10. Paper Issues or Caveats
11. Detailed Formalization Evidence
12. Paper Assumption Provenance
13. Displayed Formula Provenance
14. Library Lift Pass
15. DAG Audit
16. Validation Checks
17. Paper Definitions Checked
18. Named Theorem Statements Checked
19. Paper-Facing Statement Validator Ledger

Keep the paper-interface review sections at the end. Do not leave placeholders
or pointer prose such as "where those sections belong"; fill every section
with final human-facing content, even if that content is `None`.

### Human Verdict

Write two to four sentences for a non-Lean reader. State the current
formalization status, the main remaining mathematical/library boundary if any,
whether a paper-correctness issue is being claimed, and whether human dashboard
sign-off exists. Do not include Lean declaration names, validator row counts,
audit digests, source-record inventories, command outputs, or LOC numbers here.

### Closeout Status

Include compact facts before detailed proof evidence:

- Completion status: `formalized`, `formalized with caveat`,
  `partially formalized`, or `not formalized`.
- One-sentence recap that does not repeat the full human verdict.
- Lean footprint: total paper-local Lean LOC, `PaperInterface.lean` LOC, and
  human-review row/declaration count.
- Audit summary: source coverage/source-to-Lean counts; LLM-as-judge
  statement-match status, Lean-to-TeX row count, assumption-provenance status,
  source-record classification counts, source-record boundary/recursion
  counts, review-surface status, holistic source-first audit result, and
  DAG/source-json audit result.

The post-validation summary should include the Lean LOC line; do not bury it in
a later evidence table only.

### Researcher Summary of Checked Results

Keep this short: normally 3-6 paper-language bullets, one per major source
definition/result cluster. If it starts listing subclaims, helper formulas, row
counts, source-record packages, or implementation route details, move that
material to `Detailed Formalization Evidence`.

### Remaining Boundaries and Gaps

Write `None` when no theorem-level mathematical or library boundary remains.
Do not turn source-record audit counts, human dashboard sign-off, or
conditionally covered helper formula rows into gaps by default. Put
source-record counts under validation evidence, human dashboard status in the
verdict/review-surface note, and helper-formula explanations in detailed
evidence or displayed-formula provenance.

### Additional Assumptions Beyond Paper

List only non-source assumptions that the Lean endpoint needs beyond the paper.
Do not list source-level parameters, paper model primitives, or conditional
theorem hypotheses that are genuinely part of the paper statement or algorithm
condition. Those belong in source/scope, assumption provenance, formula
provenance, or theorem statements.

### Proof-Strategy Deviations

Use this section only for human-facing mathematical departures from the source
paper's proof route or theorem statement. Each entry must state:

- the source paper's original approach,
- the substantively different Lean proof route, and
- why the difference matters.

These entries should be rare. If there is no substantive source-proof
departure, write `None.`.

Do not list source-record packages, certificate plumbing, proof adapter names,
declaration inventories, audit architecture, dashboard parser changes,
downstream reuse of another paper's checked theorem route, named exposure of a
source condition, formula/theorem row splitting, explicit source-level theorem
parameters, conditional theorem hypotheses copied from the paper, or other
proof-organization notes here. Put those items in `Source and Scope`,
`Detailed Formalization Evidence`, `Proof Tricks Worth Reusing`, or the
relevant audit sidecar instead. If the only differences are explicit
formalization boundaries, write `None beyond the formalization boundaries
already recorded above` and point to the assumptions/gaps sections.

### Detailed Formalization Evidence

Use this section for proof-organization notes that are not deviations, such as
downstream reuse of another paper's checked route, named exposure of source
conditions, source-parameter/formula rows read inside an algorithm or theorem
rather than as standalone paper theorems, and source-record field inventories
that help future auditors but do not change the theorem statement.

### Paper Assumption Provenance

Every non-derived paper-facing theorem premise should be named in
`Assumptions.lean`, listed in `status.json` under
`review_surface.assumption_names`, and checked in `assumption_match_llm.json`.
The source-assumption judge must work at premise granularity. A grouped
assumption declaration may summarize a family of conditions, but every exact
`-- audit-premise:` comment needs a `premise_judgments` entry.

Use `partial_boundary` for visible external, library, analytic, runtime,
solver, theorem-import, certificate, process, or source-model boundaries that
remain undischarged. Do not downgrade those to `documented_caveat` unless the
source statement itself needs a repair.

### Displayed Formula Provenance

Every displayed or source-defining formula used by a named result should have
an exact paper-facing row or exact subclaim row. Broad aggregate rows are not
enough for full validation. Formula rows are closed only when the formula is
derived in Lean from source primitives or from separately validated paper
assumptions.

### Validation Checks

Summarize build/audit/DAG/no-placeholder outcomes in prose. It is acceptable to
include the exact targeted repository audit command here, but keep commands out
of the executive verdict and proof narrative.

For public reports, include the generated `### LLM-as-Judge Results` block
under this section. It must summarize every tracked judge/support sidecar:
`paper_coverage_llm.json`, `statement_match_llm.json`,
`lean_to_tex_llm.json`, `assumption_match_llm.json` when present,
`source_record_match_llm.json` when present, `source_record_audit.json`,
`review_surface_llm.json`, `docs/AGENT_SOURCE_AUDIT.md`, and the public
DAG/source/source-json audit. Use the refresh script rather than editing those
counts by hand.

## DAG and Source-JSON Audit

The DAG is a human-readable proof roadmap over the source inventory, not a
Lean implementation changelog. Before closeout, compare:

- the source paper and source-block inventory,
- `paper_statement_map.json`,
- `paper_coverage_llm.json`,
- `PaperInterface.lean` / dashboard rows,
- `docs/DependencyDAG.tex`, and
- the rendered `docs/DependencyDAG.pdf`.

Every source-named paper definition, lemma, proposition, theorem, corollary,
and appendix result in the source inventory should be represented by a visible
DAG node, unless the final report gives an explicit source-facing reason for
omission. Grouping is allowed for tight paper-result clusters, helper formula
rows, source parameters, or algorithm-condition rows, but the grouped node or
the final report/audit note must make the grouping legible. A scope note alone
must never be the only place a named source result appears.

Record a separate DAG/source-json result at closeout. It should state:

- whether the rendered DAG matches the source-inventory sidecar at the
  paper-result-cluster level,
- whether any formula/helper rows are intentionally grouped inside definition,
  algorithm, theorem, proposition, or source-parameter nodes,
- whether the DAG omits, adds, strengthens, or weakens any source-facing
  result, and
- whether the rendered PDF was visually inspected for node overlap,
  label overlap, and arrow-through-text problems.

For partial papers, the DAG must make partiality visible. Do not publish an
all-green DAG for a partially formalized paper unless the partial item is not a
paper-facing theorem target and the source inventory/final report says why.

Green/formalized nodes should summarize the paper claim, not helper families,
certificate layers, bridge declarations, compatibility routes, or old proof
attempts. Do not put Lean declaration names, `\texttt{...}` code labels,
wildcard declaration families, or implementation identifiers in visual DAG
nodes. Put those details in proof notes, the final report, or audit ledgers.

## LOC Sourcing

Every final validation report should include:

- total lines across paper-local `.lean` files,
- `PaperInterface.lean` line count, and
- the number of human-review rows/declarations exposed there.

The total paper-local Lean LOC is the proof footprint and is the value exported
as `lean_loc` / `Full proof LOC`. It is intentionally different from the
smaller interface line count. Never use the interface line count as the paper
proof LOC.

If a paper, website, manuscript, or LaTeX macro reports proof LOC, source it
from the same generated status metadata as the website, such as
`papers/human_status.json`, `papers/status.json`, or generated status tables.
Do not hand-maintain a separate manuscript LOC number.

## Post-Formalization Audit Note

Use `docs/POST_FORMALIZATION_AUDIT.md` or another agent-facing note for durable
audit details that would make the human final report too long:

- source-convention details,
- source-record field inventories,
- warnings meant mainly to prevent future agent confusion,
- long source-line mappings,
- detailed DAG/source-json comparisons,
- implementation-route history, and
- command transcripts or diagnostic notes.

Keep `FINAL_VALIDATION_REPORT.md` concise. Include audit-note material in the
human report only when it changes the theorem statement, requires an additional
assumption, identifies a source-paper issue, or explains a real remaining
boundary.

## Notes vs. Gaps vs. Deviations

Use these classifications consistently:

- **Gap / remaining boundary:** a theorem-level mathematical, library,
  analytic, runtime, solver, external theorem, source-model, or certificate
  boundary that remains undischarged for a claimed paper result.
- **Additional assumption:** a non-source condition that the Lean theorem needs
  beyond the paper, if the human has approved or the report is explicitly
  marking it as beyond-paper.
- **Source condition:** a parameter, model primitive, algorithm condition, or
  conditional theorem hypothesis stated by the paper. This is not a gap,
  deviation, or additional assumption merely because Lean exposes it.
- **Proof-strategy deviation:** a substantive mathematical difference between
  the source proof route and the Lean proof route. It must name both routes.
- **Source note / proof-organization note:** information useful for readers or
  future agents that does not change the theorem statement and is not proof
  debt. Put it in source/scope, detailed evidence, proof tricks, or audit notes.
- **Paper issue or caveat:** a real source discrepancy, corrected statement,
  indispensable non-source assumption, or source theorem repair that changes
  what is being claimed.

Examples:

- "Human dashboard sign-off remains pending" is a review-process note, not a
  Lean proof gap.
- "The source-record audit reports zero boundary inputs and zero recursion
  failures" belongs in validation evidence, not remaining gaps.
- "Two source-inventory helper formula rows are conditionally covered because
  they are read inside Algorithm 7's source parameters" is a detailed-evidence
  or displayed-formula-provenance note, not a gap, when the paper theorem is
  otherwise closed.
- "Theorem 2.2 exposes Algorithm 4's source pairwise condition as a named paper
  formula before proving the containment endpoint" is source-faithful interface
  design, not a proof-strategy deviation.
- "DGJ26 reuses DGJ24's checked SmartAllocation support-count route" is a
  downstream reuse/proof-organization note unless the source proof route is
  substantively different and the report explains both routes.

## Public PR Closeout

Before a public PR, confirm the target public checkout has the paper-local
status, DAG source/rendered PDF, final report, source-audit note, LLM sidecars,
and generated status surfaces in sync. Stage explicit path lists only. Do not
copy private source PDFs/text caches or unpublished paper folders into public.
