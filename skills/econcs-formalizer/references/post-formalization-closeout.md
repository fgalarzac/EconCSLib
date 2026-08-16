# Post-Formalization Closeout

`config/formalization_audit_protocol.json` is the normative machine-readable
policy for this workflow. This reference defers to it for current v10/v11 lane
roles, normal/deep source scope, item-level reuse, build selection, and
assumption/correction categories. Historical sidecar schema numbers mentioned
below do not redefine the current protocol.

Read this file before declaring a paper done, running a
post-validation/post-formalization pass, preparing a public PR closeout, or
editing a paper's final validation report after a completed proof phase. Do not
run this workflow for routine in-progress proof loops unless the user asks for
post-validation.

Proof campaigns are proof-first: establish the source receipt, selected
item/dependency map, audited interface skeleton, and next proof seam, then work
on proofs. Update this documentation or paper-local reports only when source
scope changes, an obligation is resolved or created, status changes, or the
paper reaches closeout.

Keep this as the operational closeout reference. The final report, audit
sidecars, source-first audit, DAG/source-json comparison, LOC sourcing, and
note/gap/deviation classification are one coherent workflow. The exact
paper-local closure artifact is deliberately specified in the companion
`references/final-closure-receipt.md`; split only DAG-specific visual/layout
rules further if needed.

The single paper-local closure artifact is `FINAL_CLOSURE_RECEIPT.md`; read
[`final-closure-receipt.md`](final-closure-receipt.md) before declaring a paper
closeout-complete or release-ready. The final validation report is the
mathematical summary and all audit sidecars/ledgers are its evidence inputs; do
not treat any of them as competing final receipts.

Use [`../../../docs/FORMALIZATION_STATUS_POLICY.md`](../../../docs/FORMALIZATION_STATUS_POLICY.md)
for every status decision. In particular, reserve `formalized with caveat` for
a substantial source-paper error with a fully proved corrected endpoint. A
weaker Lean target or added non-source assumption is partial; a minor repair
with an unchanged substantive endpoint is a note on plain `formalized` work.

## Closeout Gate

Operational closeout improvements are compatibility-preserving by default.
Keep them in a commit that does not change audit prompt/protocol/schema/producer
identities or tracked paper receipts. A genuine semantic-producer change is a
separate change with an explicit semantically selected affected-paper set; it
must not make every previously closed paper stale merely because shared code
was edited.
The durable protocol identity is the structured
`formalization_review_protocol_sha256`. A semantic-meaning correction must bump
a field retained by that digest; prose, refactors, diagnostics, and performance
work outside a lane's pinned producer surface may invalidate only ignored
scheduling cache. Lane-specific semantic versions and raw-producer identities
remain authoritative; the engine ledger does not override them.

### Normative operator loop

Items 1-20 below prepare one frozen closeout; item 21 starts the
planner-driven execution loop. Neither list is a batch of commands.

1. Finish every tracked proof, sidecar, report, DAG, and paper-local status edit.
2. Freeze those inputs, then run `closeout_reuse_plan.py` as the first closeout command.
3. Execute only `next_action`; the `actions` array is explanatory, not a batch queue.
4. Run an `after_*` successor only after its named predecessor, and replan only at an explicit replan action.
5. Treat every `inspect_*` action as a stop-and-inspect result, never as launch permission.
6. If a failure requires a tracked edit, repair it, freeze again, and make one new plan. After a pass, do not append dates, transcripts, or status prose to tracked paper files.

### Planner ordering and no-repeat rule

Use `closeout_reuse_plan.py --paper <paper>` as the sole normal closeout
entrypoint. It first checks cheap deterministic paper-local readiness and the
controlled full-closeout status. Only an eligible paper pays the exact
source-artifact/intake scan, followed by the bounded saved raw/judgment
identity check, exact item-level reuse, a paper-root warm-up build only if
scheduled, a manifest batch only if scheduled, and one fresh strict closeout.
Do not run a dashboard refresh, raw audit, build, or direct
`audit_repository.py --paper-closeout` command between those stages unless the
plan names that action or a named failure is being diagnosed.

The controlled `Completion status` in `status.json` and the final report
describes the mathematical scope claimed by the paper-facing interface. It
makes a completed paper eligible for this procedure; it is not the closure
receipt. The current `FINAL_CLOSURE_RECEIPT.md` binds the selected evidence lane
and frozen input set. The planner/worker terminal record is execution evidence
for producing that receipt, not a second paper-local final verdict. Do not
silently turn a pending rebind, raw refresh, or worker recovery into a
mathematical downgrade, and do not describe a stale receipt as a newly
discovered theorem boundary. Conversely, do not call a paper closeout-complete
or release-ready until its current closure receipt validates. Keep transient
retries in planner/worker state rather than a human-facing final report.

`--diagnose` is read-only nonsemantic diagnosis. It reports an active or
recoverable worker state, audit-engine registration, static paper-local
readiness, and status eligibility together in dependency order. It never reads
semantic caches, runs raw identity work, writes a plan, or grants acceptance.
Resolve the listed blockers, including any registered engine transition, before
a normal planner run.

The bounded raw preflight has three non-accepting outcomes. A current raw
receipt with a differently bound judgment sidecar requires review of that
current semantic delta only. A stale raw receipt requires one freeze followed
by one raw reissue. An indeterminate or noncanonical configured raw receipt is
an `inspect_*` stop, not permission to reissue or build. This ordering prevents
expensive Lean work from preceding a source-evidence repair that will invalidate
it anyway.

A fourth, equally narrow route is a **current semantic-surface repair**: the
raw source/configuration identity is current, raw receipt/scan/item metadata
are valid, the raw bytes are stable, and only the generated semantic surface is
invalid. Execute `repair_current_source_record_semantic_surface` or the exact
authenticated structural replay it names, then replan; do not reissue the same
raw. This classification is a closed structured receipt state, never a match
on an error message, paper ID, declaration name, row name, or function name.
Any mixed or unavailable dimension remains an inspection stop.

A current raw receipt with an absent, unreadable, or malformed judgment
sidecar is a judgment-reconstruction action, not a raw reissue. When the plan
does schedule `freeze_then_raw_reissue`, execute its dedicated wrapper exactly:

```bash
python3 scripts/closeout_reuse_plan.py --paper <paper> --execute-freeze-raw-reissue
```

The planner checks the producer's read-only repository scan lock only after it
has classified the raw as stale. If another scan holds it, the next action is
`wait_for_source_record_scan`, not a runnable reissue: wait for that scan and
then execute its explicit replan successor. The wrapper repeats that check
before it preserves predecessor bytes or launches the producer. A lock race is
also reported as a wait when the producer confirms a current holder. Do not
retry a raw action merely because a terminal stream disappeared.

In a multi-paper closeout wave, treat `freeze_then_raw_reissue` and the owning
paper's immediately scheduled current-identity/delta materialization or replan
as one serialized source-record lane. Do not start another paper's raw reissue
between those two steps. This does not make later human semantic judgment a
repository-wide lock: first materialize its exact worklist, then release the
raw lane for the next paper. The normal wrapper also owns a short-lived
repository transition lease: when another wrapper owns it, wait and replan
rather than preserving a second predecessor or racing the raw producer. The
lease is operational only; the producer's own evidence lock remains
authoritative for raw publication.

An authenticated overlay whose live identity replay is temporarily unavailable
is neither empty nor stale. Defer the manual-complement/template operation and
retry after the evidence lock is released; never write a full manual worklist
by interpreting a busy optional transport as an empty one. A genuinely invalid
or stale optional transport still contributes no reuse credit and fails closed.

When the lock is available, the wrapper verifies eligibility and exact intake
again, preserves the replaceable raw/judgment predecessor bytes in ignored
recovery state, invokes the producer once with its exact schema-10 cache
policy, and stops for a new semantic-delta judgment. Do not substitute a
generic raw-audit invocation or write/bind a judgment sidecar within this
transition.

When a raw reissue is scheduled, preserve this exact sub-order: freeze the
source/map/interface/status inputs; issue one raw candidate; validate any
authenticated structural replay against that exact raw/map pair; compute the
effective raw semantic surface; then calculate descriptor reuse and materialize
only the unresolved current semantic complement. Do not materialize a judgment
sidecar before the effective raw surface is valid. A changed frozen input means
return to the planner; an unchanged failure is an inspection result, not a
reason to reissue the same raw receipt.

Before retrying an unavailable source-record scan, run the read-only command
below. Its owner metadata is diagnostic only because sandbox PID namespaces may
hide a live worker. Never unlink, replace, or automatically reclaim the lock:

```bash
python3 skills/econcs-formalizer/scripts/source_record_audit.py --root . --lock-status
```

The source-record lock serializes expensive scans only. A current receipt may
reuse the lock-free bounded identity path; a stale receipt waits for the holder
and then performs the one planner-authorized reissue. Keep candidate raw,
template, and scratch files in ignored work areas. Canonical `audit/` files are
the accepted current receipt, its associated judgment sidecar, and any
authenticated structural witness, not a collection of retry attempts.

Persisted-manifest revalidation uses a memory-safe one-root Lean batch by
default. Do not change `ECONCSLIB_MANIFEST_BATCH_SIZE` for a live scan. A later
paper may use a larger bounded value only after a representative batch-one
comparison records matching per-root receipts, peak memory, and successful
return codes; batching is scheduling, never evidence reuse.

Within one raw-audit process, an already successful compact revalidation may be
reused only under the identical complete compiled-context coordinate. This
avoids duplicate Lean requests from independent consumers while preserving
their separate acceptance checks. Failed or absent output is never cached; the
memo is process-local, returns isolated copies, is not persisted, and is not
evidence. While another source-record scan owns the repository lease, use its
phase metadata for operational diagnosis rather than inferring work from shared
scratch files.

For every new or refreshed full closeout, the `Closeout Status` section
of the final report must contain exactly one controlled-vocabulary completion
status matching `status.json`. A legacy report lacking that line receives a
one-line front-matter alignment repair before its next closeout; that repair is
not a semantic audit refresh. No historical quote, code block, or generated
ledger may be used as the current whole-paper verdict.

Ignored operational state is non-authoritative but not disposable. Do not
manually delete, edit, or copy worker state/log pointers, identity-addressed
plan receipts, compiled/content guard caches, or profile-specific legacy
adoption files during recovery. Inspect through the planner and
`run_paper_closeout.py --status`; deleting state loses idempotence and can
recreate work.

### Audit-engine changes

Stage the exact candidate production code and any structured protocol change,
then generate the next append-only engine entry with
`check_formalization_engine_revision.py --index --print-update --rationale ...
--verification ...`. Replace only the ledger with that generated output, stage
it, and run the checker again with `--index`. Never edit a prior entry.
`review_compatible` means identical review obligations and accept/reject
meaning; runtime, diagnostics, and orchestration alone may qualify. Any change
that can alter semantic obligations or acceptance must first change the
structured protocol. Registering the engine transition does not rewrite or
rerun a paper, and it does not waive a lane-specific producer pin.
Commit that registered transition before planning or launching a closeout.
The runtime gate requires production engine sources and the ledger to match
clean `HEAD` (including no ignored/untracked source or index flag that hides
changes), permits
only structured-projection-neutral protocol prose drift, and validates the
exact committed engine revision. It runs before receipt reuse and again before
a worker success is accepted. The gate and ledger remain operational: a
`review_compatible` registration does not by itself enter or stale paper
receipts or plan identity. Exact lane-specific raw-producer and Lean-control
pins remain additional, stricter layers and still invalidate their own selected
receipt when those exact inputs change.

Batch and register any raw-producer edit before launching a closeout wave; do
not edit it while `source_record_audit.py --lock-status` reports a held scan.
The producer recomputes its input fingerprint before publication and rejects a
mixed-input candidate. That preserves integrity, but an avoidable mid-scan
edit wastes a long Lean pass and must not be treated as a reason to retry
automatically.

At closeout, verify the target paper only. Do not rerun all-paper
LLM-as-judge jobs unless the user explicitly asks for an all-paper refresh.

The required Lean validation receipt for a paper closeout is its paper root
target. The consolidated strict closeout owns that receipt. Run this standalone
command first only when the reuse planner schedules a build or when diagnosing
a build failure:

```bash
env LEAN_NUM_THREADS=1 lake build <Paper>
```

This is the paper build: it validates the paper's delivered root module,
including its `PaperInterface.lean` and required paper-local imports. An
interface-only build is useful during a proof edit loop, but it does not replace
the closeout receipt. Do not substitute a package or repository build as the
ordinary closeout default. Widen the build only when a paper-specific dependency
reason requires a module outside that closure; record that reason and the
additional target in the validation receipt. A full package or repository build
remains an integration/release check or an explicit user request, not evidence
required for an ordinary paper closeout.

The stateful strict-audit child validates the exact planner receipt before it
acquires execution state, and the runner revalidates it after the audit child
exits. The launcher does not duplicate that entry replay for a new worker. A
completed worker may be reused only when its terminal state and the same current
plan receipt both validate. A stateful direct
`audit_repository.py --paper-closeout` invocation is intentionally rejected
without a current planner-issued receipt; use `--no-closeout-state` only for a
named diagnostic and re-enter through the planner afterward.

For completed papers whose paper-local status explicitly sets
`repository_visibility: public`, the fast diagnostics also accept
`--public-complete` in `audit_conclusion_provenance.py` and
`audit_evidence_integrity.py`. That selector includes both `formalized` and the
rare `formalized with caveat` status. It is a batch alarm surface only: every
paper still needs its own source-first review and final `--paper-closeout`
receipt. During the 2026-07-18 migration, use the frozen inventory and live
dispositions in
[`../../../docs/PUBLIC_COMPLETE_PROTOCOL_AUDIT_2026-07-18.md`](../../../docs/PUBLIC_COMPLETE_PROTOCOL_AUDIT_2026-07-18.md)
so a paper reclassified as partial does not disappear silently from the audit.

### Preparation and execution checklist

Complete preparation items 1-20 before starting final execution in item 21.

Runtime discipline follows one statement freeze:

- finalize one exact source inventory, `PaperInterface.lean` surface, and
  declaration manifest;
- retain every sidecar item whose exact semantic identity is current, and
  generate only affected items from that frozen manifest;
- update paper-local reports and the DAG, then render/check only the selected
  paper's owned status output with `sync_paper_status.py --paper <paper>`;
- defer aggregate JSON, Markdown, site, and all-paper dashboard reconciliation
  to integration/public-PR/release preparation;
- finish with one targeted strict paper closeout.

The statement/source-to-Lean/coverage/assumption strict commands are diagnostic
lanes, not four mandatory reruns after a consolidated closeout passes. A
docs-only edit after statement freeze needs report/status consistency checks,
not semantic-manifest or statement-sidecar regeneration. Run manifest-heavy
commands serially, retain the original process/session handle, and poll known
long jobs at coarse intervals rather than restarting or repeatedly probing a
quiet Lean elaboration.

1. Reject every remaining statement-skeleton proof hole. A private intake
   theorem may have used `by sorry` so its type could be audited first, but
   closeout requires zero `sorry`, `admit`, `axiom`, `opaque`, or `constant`
   proof shortcuts in the paper dependency closure. Confirm that the current
   fully elaborated signature/dependency identity is the one audited before
   proof implementation.
2. Freeze the source receipt, selected source items, and paper-facing Lean
   surface for the target paper. Normal checks are read-only. Run one explicit
   per-item refresh only after the semantic source and Lean inputs for the
   affected items are stable.
3. Confirm the human entrypoint stays compact. `PaperInterface.lean` is the
   only supported row-level dashboard and LLM audit surface. If the supporting
   proof/API surface is large, move proof plumbing and helper endpoints to
   `AuditInterface.lean`, `ProofInterface.lean`, or implementation modules, but
   keep the audited paper-facing wrapper statements in `PaperInterface.lean`.
   Write those wrappers with direct source formulas whenever practical. Deep
   chains of adapter projections can make manifest canonicalization take
   minutes even when the mathematical statement is small; moving the adapters
   out of `PaperInterface.lean` and exposing the same elaborated formula
   directly preserves semantic auditing while substantially reducing refresh
   latency.
4. Confirm every declaration in the configured review surface is classified in
   `status.json` under `review_surface.include_names`,
   `review_surface.assumption_names`, or `review_surface.auxiliary_names`.
5. Build or refresh a source-curated `audit/paper_statement_map.json` from the
   source paper, not from Lean row names. For public-facing statuses, a missing
   explicit source inventory is a closeout blocker. First create an independent
   named-presentation receipt from a canonical text/TeX artifact, pinned by
   path, SHA-256, and index digest. The normal
   `named_theoretical_statements` surface is independently source-presented
   named definitions, results, theorem-like claims, explicitly named
   assumptions/model conditions, and named appendix theory. Standalone
   formulas, equations, algorithms, figures, tables, captions, numerical
   examples, simulations, empirical material, computational results, and other
   prose belong only to an explicit `deep_paper_with_all_prose_claims` audit as
   independent items. They are still inspected when a selected named result
   depends on them.

   Configure nonstandard source environments/headings declaratively in the
   receipt. An unclassified named presentation blocks closeout. Record a named
   open problem with an explicit source-declared-open nonproof disposition;
   never silently omit it or demand a theorem proof for it. Every selected item
   and premise needs a resolvable source locator and source evidence. A source
   PDF or archive may establish provenance, but the normal-mode index must be
   reproducible from a reviewable canonical text/TeX artifact.

   The source inventory and coverage sidecars must not use map keys, Lean row
   names, aliases, or imported declaration names as semantic evidence. Each
   covered source item needs a source semantic identity and a unique current
   fully elaborated Lean signature/dependency identity, plus a source-grounded
   explanation of the correspondence. If a reusable library declaration is
   involved, expose the source-to-library equivalence on the reviewed surface;
   an imported name or source-shaped wrapper is not evidence.

   Treat every claimed source-row/`PaperInterface` association as a semantic
   relation, never as a positional zip. Associations claimed one-to-one must be
   exact bijections over the selected semantic identities; represent intentional
   fan-out explicitly. Do not synthesize a missing source claim from a Lean type,
   binder, or theorem. A transparent `Spec : Prop` may support direct structural
   comparison and routing, but it receives no independent proof credit: the
   reviewed theorem's elaborated type and proof closure must establish the
   endpoint.

   For a new or materially refreshed closeout, keep the v10 statement/source
   atom lane current and set
   `source_claim_atoms_schema: 1` in that map and
   `review_surface.llm_statement_review.require_source_claim_atoms: true`.
   Every canonical theorem-like item needs source-first atoms with a stable id,
   exact source locator, substantive semantic claim, and one reviewed Lean
   theorem/lemma route. Extract all clauses from the pinned source statement
   before looking at the Lean surface, then independently check that no
   existence, uniqueness, scope, formula, algorithmic, or all-optima clause is
   missing. A route is navigation to an already audited PaperInterface theorem;
   a record, certificate, source model, definition, abbreviation, assumption,
   or hidden helper cannot certify an atom. Legacy maps without the versioned
   opt-in remain compatible only until a material closeout refresh. New
   closeouts and explicit v11 upgrades also complete the v11
   theorem-realization correspondence; current v10 evidence is not v11
   evidence by relabelling. A legacy material repair receives current
   item-level v10 evidence unless it explicitly upgrades.
6. Verify `paper_coverage_llm.json` against source semantic identities and
   current fully elaborated Lean signatures. This paper-level source-to-Lean
   lane is the only LLM-as-judge lane that says whether every selected source
   item is represented; dashboard names are navigation only.
7. Verify `lean_to_tex_llm.json` for every current non-assumption review row
   using current elaborated signature identities.
8. Verify `statement_match_llm.json` with the strict full-statement,
   exact-formula prompt. The raw row judgment should stay strict:
   intentionally accepted conditional rows remain `mismatch` with
   `resolution: "conditional_boundary"`. Require the v10 semantic obligation
   ledger to enumerate source and Lean assumptions/conclusions, recover every
   source conclusion, and justify every Lean assumption using exact source
   locators and explicit mathematical bridge statements. Gap lists contain
   obligation ids. A conditional boundary may account for an extra Lean
   assumption but never an unmatched/weakened source conclusion. Declaration,
   record, and field names are routing, not evidence.
9. Verify `assumption_match_llm.json` for every assumption and proof-boundary
   name. Source-assumption provenance must work at premise granularity through
   `premise_judgments`.
10. During active semantic review, generate or refresh the code-backed recursive
   source-record audit for every affected row whose statement or visible
   premises mention a record, certificate, replay, process, bridge, source
   model, source row, or consequence package. Save
   `source_record_audit.json` and refresh `source_record_match_llm.json` only
   for missing, stale, or structurally changed target-paper rows. If those
   inputs are already frozen for closeout, do not run the producer by hand: the
   planner decides whether the current raw receipt is reusable, needs a
   judgment-only repair, or needs its one raw transition.
   Each predicate, structure, inductive, certificate, or process row must record
   its expansion basis and transitive result-bearing dependencies. A `matches`
   verdict is invalid while required recursive expansion is incomplete. Review
   only the semantic dimensions triggered by the actual source and Lean
   statements, such as numeric boundary behavior, discrete/order behavior,
   output shape, witness/existence conditions, cardinality, execution scope, or
   model semantics. Each applicable match must be bound to an explicit Lean
   conclusion; do not require a fixed domain-specific checklist for rows that do
   not trigger it.
   After actually reviewing and updating `source_record_match_llm.json` during
   active review, reconcile the judgment-derived counts and
   conclusion-dependency resolutions without a second Lean elaboration:
   `python3 skills/econcs-formalizer/scripts/source_record_audit.py --paper
   <paper-folder> --root . --out
   papers/<paper-folder>/audit/source_record_audit.json
   --refresh-judgment-summary`. This preserves the prior successful
   `lean_check`; it does not replace the initial Lean-backed generation and is
   not a routine frozen-closeout step.
11. Inspect source-record classifications before setting status. Remaining
   `approved_external_boundary`, `unresolved_assumed_math`, stale
   source-record digests, or missing source-record judgments make the affected
    row partial/conditional unless Lean has discharged the field or the status
    claim explicitly excludes that source item.
    Use `visible_boundary_component` only for recursive fields exactly unpacked
    from visible theorem premises, and `derived_from_visible_boundary` only for
    recursive fields Lean derives from visible theorem premises; neither may be
    used for theorem-boundary inputs themselves.
    Confirm the recursive helper unfolds paper-facing `abbrev` aliases before
    deciding that a record-backed row has no boundary fields. A certificate,
    replay, run, or source record must have a Lean-checked constructor from
    source primitives; projecting its conclusion-bearing fields is not a proof
    of the paper claim.
12. Run a proof-level library-lift pass. Extract small, targeted generic
    lemmas/results when the destination is clear and the relevant builds can be
    checked; otherwise record the candidate and destination module in the final
    report.
13. Run a final easy-extension pass after the Lean proof route is known.
    Re-read the paper claims and final formal endpoints, then ask which
    generalizations, conjectures, or extensions are trivial or near-trivial:
    weakened assumptions, immediate corollaries, stronger conclusions, or
    natural adjacent conjectures. Prove only cheap extensions that do not
    distract from source closeout, and record both proved and deferred
    candidates in the final report.
14. Run a skill-update pass. If the paper taught a reusable workflow lesson,
    update this skill or an appropriate reference before final handoff; if it
    did not, state that explicitly in the final report or handoff.
15. Update `docs/DependencyDAG.tex`, render `docs/DependencyDAG.pdf`, visually inspect
    it, and record the DAG evidence in the final report and post-formalization
    audit note.
16. Write or refresh `docs/AGENT_SOURCE_AUDIT.md` as an independent source-first
    holistic audit. It must read the source first, build or verify the source
    inventory from the source itself, then inspect `PaperInterface.lean` and
    Lean statements for omissions, hidden strengthening/weakening, and semantic
    mismatches. It must not merely summarize existing sidecars. Write
    `## Overall status: PASS` only when the independent source-first audit
    agrees that the claimed source surface is covered.
17. If the paper is being prepared for public release or a final non-active
    private closeout, remove it from `papers/audit_config.json`
    `active_papers` after the review surface, source inventory, LLM sidecars,
    DAG, and final report are current. The active-paper list is for unfinished
    proof work only; leaving a completed paper there hides it from routine
    repository-wide statement and coverage gates.
18. Record every already-known unresolved `mismatch`, accepted
    `conditional_boundary`, `uncertain`, stale, missing, or broad-surface
    finding in the final report. If final execution discovers a new material
    finding, repair and document it, restart at the first invalidated
    preparation item, freeze again, and return to item 21 through a new plan.
    Do not edit the tracked report after a zero-error closeout or rerun every
    individual dashboard lane unless diagnosing a named failure.
19. Update paper-local `status.json` with the DAG and final report, then run
    `python3 scripts/sync_paper_status.py --paper <paper-folder>` and its
    `--check` form. This updates only paper-owned output. Run the unscoped
    status sync later when preparing aggregate status, the website, a public
    PR, or a release.
    If a completed paper configures `audit/source_proof_fidelity.json`, upgrade
    it to schema 2 and give every defect a `status_impact` and
    `status_impact_rationale`. Check that those issue-level classifications
    agree with the paper status before regenerating any public surface.
    The root `README.md` is protected hand-written prose and must not be edited
    during closeout unless the user gives specific root-README instructions.
20. Refresh the final-report LLM-as-judge summary block from the sidecars. In
    the public repository, run
    `python3 scripts/refresh_validation_report_audit_summaries.py` and then
    `python3 scripts/refresh_validation_report_audit_summaries.py --check`.
    The refresher reports counts only. It must never manufacture holistic or
    DAG `PASS` language; those verdicts require their own tracked, current audit
    artifacts.
    Render from one frozen report-input snapshot, validate receipt-authorized
    semantic totals, and label non-receipt evidence as recorded rather than
    freshly authorized. Recheck saved-status authority and all report inputs
    before publication, then use the checked staged write with flush and atomic
    replacement. Never publish from an editable cache or a partially refreshed
    set of inputs.
    Do not hand-write that source coverage, statement-match, Lean-to-TeX,
    assumption-provenance, source-record, review-surface, holistic, or DAG
    result text; if a sidecar exists, the report must not say it is "not
    separately recorded".
21. Run final execution only after preparation items 1-20 are complete.

    **Plan.** Run `python3 scripts/closeout_reuse_plan.py --paper
    <paper-folder>`. It uses the canonical item-level reuse context, reports new
    and retired obligations, and distinguishes a missing compiled cache from
    changed human semantics. Refresh only its listed items. Its default output
    suppresses successful item receipts while retaining all repair obligations;
    request `--all-items` only for a full inventory.

    Existing audited items that predate entry-local reuse pins remain eligible
    for the current closeout after full in-memory validation. Do not rewrite
    their sidecars or rerun their audits merely to seal future-reuse metadata;
    do that only at the next intentional semantic refresh. New-paper intake
    should write the pins prospectively. Existing papers without the
    prospective `audit/intake_freeze.json` marker are grandfathered only when
    they belong to the trusted pre-rollout cohort. Never backfill the marker or
    reopen those papers for it. Removing the marker from a newly scaffolded
    paper is an intake failure, not a downgrade to legacy.

    **Execute.** Do not run a dashboard `--precheck` merely for a summary at
    this stage. Execute only the plan's current `next_action`; use precheck
    earlier only to diagnose a named failure, then freeze and re-enter through
    the planner. For a cache miss, continue from its build through the
    state-qualified one manifest
    refresh and explicit replan boundary; do not rerun the planner between
    build and refresh. A rebuilt artifact must replan before closeout. Semantic
    failures are a manual worklist, not an automatic review command.

    If the plan schedules `strict_closeout`, run that exact argv, retaining its
    audit profile, `--plan-identity`, and `--new-run` disposition. An inspect
    action for an exact current completion is the stopping action; do not launch
    a new gate. The consolidated acceptance command runs evidence integrity and
    conclusion provenance after the primary paper gate passes, in the same
    process and with the same mutation-guarded source-record and Lean
    identities. It stops before a later expensive lane when an earlier lane has
    already failed. Do not rerun the two component commands after a passing
    consolidated closeout.

    **Recover.** The detached launcher atomically maintains ignored operational
    state at
    `papers/<paper-folder>/.review_traces/paper_closeout_worker.json` and rejects
    a second live invocation. If a terminal/session stream is lost, inspect
    that file and its immutable launch-specific worker log instead of starting
    the gate again. Inspect state without launching work via `python3
    scripts/run_paper_closeout.py --paper <paper-folder> --status`.

    A known successful legacy completion gets one ignored operational material
    baseline: unchanged material is inspected rather than rerun, while a later
    material change schedules the current closeout. Unknown, incomplete, or
    failed legacy state is never auto-adopted. The persisted state is
    scheduling/recovery data, never acceptance evidence.

    A `replan_current_inputs` action carries a receipt-publication disposition.
    Retry only `source_race` or `compiled_race`, and at most once for the same
    exact input identity. `deterministic_input` and `publication_io` are
    stop-and-repair results, not a reason to spin the planner. A changed input
    identity permits one new race retry; it does not make earlier evidence
    current.

    **Accept.** Do not claim post-formalization completion while the final
    execution reports missing/stale DAG, validation-report, source-record,
    LLM-sidecar, or hidden-premise findings for that paper.

    The standalone `audit_evidence_integrity.py --paper <paper-folder>` and
    `audit_conclusion_provenance.py --paper <paper-folder>` commands are
    diagnostic lanes for a named failure. Add `--release` to the former only
    when claiming independent/human release certification; do not turn an
    honestly recorded lack of human review into proof debt or fabricate review
    to make that mode pass. A reviewed theorem may not consume its own
    conclusion, or a result/certificate/run record containing that conclusion,
    unless current Lean source contains a non-circular paper-local constructor
    from primitive inputs. A constructor that accepts the same conclusion,
    nested certificate, or conclusion fields and repackages them does not count.
    A paper-facing endpoint must also terminate in the source's advertised
    proposition or scalar outcome. An existential source-profile, execution,
    or certificate package may be constructed inside its proof, but it does not
    replace a direct source conclusion merely because projecting the package
    would yield that conclusion. Likewise, preserve a source multiset/set
    interface when an implementation uses lists internally; representation
    convenience is not a source-model equivalence.
    Genuine assumption/condition/input/model record fields remain antecedents,
    but any exception for a result-like field needs a current source-record
    judgment with an exact page/section/theorem/equation locator.

After item 21 passes, inspect the terminal state and stop. Aggregate status,
site, public-PR, and release work may consume that frozen result, but paper-local
tracked edits require a new explicit closeout boundary.

The full closeout gate is for completed papers, intentionally approved
conditional closeouts, public PR preparation, or explicit user-requested
post-validation. For unfinished active papers, use targeted Lean builds,
placeholder scans, JSON sanity checks, and row-scoped audit refreshes only for
changed rows.

If semantic review discovers an unproved mathematical step, stop the closeout
phase explicitly and reopen proof work. Record the new obligation, prove it
with targeted Lean checks, freeze the theorem surface again, and only then
resume closeout. Do not keep running audit gates while theorem files are still
changing or describe reopened proof construction as a slow audit.

## Fast, Strict Audit Scheduling

Maintain a concise validation receipt during closeout. For each expensive
check, record its target, successful exit, and the file classes that invalidate
it. Use `git diff --name-only` against the validated revision to decide what to
rerun after a compaction or interruption:

- Changes to Lean files, imports, Lake configuration, or the paper-facing
  theorem surface invalidate the relevant focused build and downstream
  semantic/provenance checks.
- Changes to `status.json`, the source map, review-surface configuration, or a
  statement/assumption ledger invalidate the corresponding dashboard and
  recursive-provenance lanes, but not an unchanged Lean build unless the Lean
  surface also changed.
- Changes only to audit JSON require JSON validation, the named affected lane,
  and the eventual final closeout; they do not require a Lean rebuild.
- Changes only to the target paper's Markdown or TeX audit prose require
  `git diff --check`, any generated-report consistency check that owns that
  prose, and the eventual final closeout; they do not invalidate builds,
  statement judgments, or source-record classifications. Workflow or skill
  prose outside the paper is not a paper closeout input.

Context compaction, elapsed time, a status request, or loss of terminal output
does not invalidate a recorded pass. Re-run only when a listed input changed or
the earlier command did not finish successfully.

`closeout_reuse_plan.py` keeps an ignored, non-authoritative advisory projection
under `.review_traces`. It binds exact direct audit/source inputs, the
Lean-graph-selected source and compiled artifact ledgers, build controls, and
the planning implementation. A cache hit avoids reparsing the large dashboard
cache. Exact byte hashes and lengths are durable compiled identity; guarded
filesystem stats only avoid rereading unchanged files. When a guard changes,
the planner hashes that repository path alone, or refreshes the exact external
aggregate, and retains the plan after an identical-byte rebuild; changed bytes
trigger replanning. The
separate completed-run identity covers the target paper's material closeout
inputs and complete target-paper Lean-file inventory, target-projected
configuration, the exact Lean-graph-selected source closure and module
ownership, build controls, external artifact routing,
compiled ledger, absent alternate source candidates, and normal/deep profile.
Ambient scratch, ignored caches, unimported Lean files outside the target paper,
unrelated library modules, and other papers' configuration are excluded.
Operational state, logs, planner
cache, skill text, and workflow scripts are excluded from semantic receipt
identities and may not force an existing paper through another audit.

The durable protocol input is the canonical structured
`formalization_review_protocol_sha256`, not Python source hashes or whole-file
protocol prose. Any correction that changes semantic audit meaning must bump a
structured audit version or compatibility field retained by that digest.
Refactors, diagnostics, documentation, and performance changes outside a
lane's pinned producer surface may invalidate only the ignored advisory cache.
Lane-specific semantic versions and raw-producer pins still apply. Never encode
semantic changes as unversioned implementation behavior.
The raw-producer identity must cover only code that can change the emitted
obligation or receipt semantics. Progress reporting, staging location,
copy-versus-hardlink transport, resource containment, and other fail-closed
execution controls are operational inputs; do not place them inside an
identity-pinned producer slice or let them reopen completed paper evidence.
Operational snapshots exclude engine files only by evidence role: an exact
raw-producer path remains material regardless of `.py`, `.lean`, or `.sh`
suffix; nonproducer implementation paths use the structured compatibility
boundary.
The append-only formalization-engine revision ledger makes that classification
explicit in CI, but its digest is operational and must not enter paper evidence,
plan identity, or material-artifact identity. Legacy Lean-closure receipts keep
their original records and hashes across a retired-control migration. Only the
exact historical three-control tuple may use that compatibility path; every
other missing/extra control fails. Do not rewrite tracked evidence or rerun a
paper to adopt the new closeout machinery.

Legacy operational adoption is profile-specific and one-time. It compares only
the selected material inputs and Lean-owned rollout graph against the trusted
rollout tree under an inode-verified lock. It must reject unknown/failed state,
the wrong paper or profile, ambiguous ownership, or a replaced lock path; a
broad diff of the paper directory is not the adoption criterion.

The planner publishes an identity-addressed receipt. Launch only the exact argv
it prints: the stateful strict-audit child requires that receipt before starting
its transaction, and the runner revalidates it after the audit child exits. The
targeted strict transaction then performs
status-routed DAG, final-report, and independent source-audit artifact checks
plus intake preflight before constructing the expensive semantic context.
Blocking artifact or intake errors fail there and warnings carry into final
findings; the full status and semantic checks remain later. Planner static
readiness checks only the explicit paper root, `PaperInterface.lean`, and
paper-local `Assumptions.lean` when present; it is an early diagnostic, not a
replacement for authoritative Lean graph or artifact validation.

Use one stable manifest per post-audit batch. First finalize the source receipt,
selected source inventory, `PaperInterface.lean`, `status.json` review surface,
and any source-facing statement change. Then update only the dependent
statement, coverage, review-surface, and provenance sidecars for items whose
source semantic identity or elaborated Lean signature changed. Update the final
report and DAG next. Refresh the dashboard only when the planner schedules it
or affected semantic items require it; otherwise retain the current cache.
Normal checks remain read-only.

Item-level reuse is valid only when the current source-semantic digest and a
unique current fully elaborated Lean signature and transitive proposition/type
dependency identity agree with the recorded item. The latter pins exact module
artifacts only for opaque imported terminals whose bodies are unavailable to
the semantic graph. Whole review-module artifacts, unrelated declarations, and
theorem proof bodies are excluded, so replacing `sorry` preserves an unchanged
statement judgment while reopening proof closure. A route, map key,
declaration name, equivalent raw Lean surface rewrite, source file, or
line-number rename may rebind only when that elaborated semantic match is
unique; refresh raw declaration text only afterward as trace evidence.
Artifact relocation alone is harmless, but every
normal source check validates each reused byte anchor against the current
artifact, including after changed bytes or locator movement. Missing pins,
changed quoted text, and ambiguous rebinding fail closed. Rebuilding a broad manifest after
each sidecar or report edit is unnecessary churn and makes small agents slow
without improving audit quality.

Lean owns both the semantic dependency graph and the repository module/import
graph used for routing. Python validates the emitted graph and exact byte pins;
it must not reconstruct import edges from source text. Cache-free reuse of an
unchanged saved closeout is valid only through an immutable receipt that binds
that exact import closure, canonical source attestation, statement and coverage
dispositions and counts, and a name-free bijection over the selected source
surface. Missing, duplicated, ambiguous, or changed semantic bindings fail
closed.

The persisted dashboard row cache is an interactive rendering and rebinding
cache, not an acceptance credential. Strict closeout performs one fresh
batched Lean manifest extraction for the selected rows, without the redundant
`#check` preview process, and then applies item-level reuse to the human
semantic judgments. Non-strict dashboard views may reuse cached rows after
exact transitive Lean-source, source-text, review-selection, and sidecar
invalidation checks. Never promote an editable cache payload into semantic
evidence merely to avoid that one batched attestation.

The planner and strict transaction must use the same worktree. In a fresh or
isolated worktree, do not invent a standalone interface-build and repeated
context-capture sequence: run the planner and follow its dependency-ordered
`next_action`. Use an interface-only build or repeated context capture only to
diagnose a named unstable-context failure. Do not create another worktree as an
ordinary closeout step.

Finalize every current v10 statement atom ledger, including configured
assumption rows, before the final recursive source-record generation. A current
atom ledger discharges ordinary visible binders once; running source-record
first creates redundant premise judgments that must be regenerated after the
statement ledger catches up. For a mathematical existence result, mark the
execution-scope dimension applicable and compare the source and Lean claims as
non-executable existence rather than leaving that dimension absent. Freeze the
compact `PaperInterface.lean` during this sequence, and treat
`ProofInterface.lean` as proof/API storage rather than a dashboard surface.

Perform one complete sidecar migration before running diagnostics. Do not run
the full statement or source-record checker after each small JSON correction:
validate the transformed JSON locally, run one row-level precheck, generate the
recursive audit once, and finish with one consolidated closeout. A failed row
names the diagnostic lane to rerun; a passing consolidated closeout does not
need each individual lane repeated.

Budget full gates by default: one consolidated diagnostic only when needed,
then one final full closeout after all fixes and documentation are frozen. If a
full closeout fails, use its named lane for intermediate diagnosis. Do not run a
third full closeout without identifying the file change that invalidated the
second receipt. This is a scheduling rule, not a waiver: the final frozen tree
still needs one complete passing closeout.

For a protocol-only statement-ledger migration, compare invariant projections
before and after: declaration and paper hashes, judgment/resolution,
obligations, source locators, premise classifications, and per-item digests.
Semantically review every newly introduced protocol dimension row by row. Do
not bulk rewrite or re-date source-record atom judgments merely to match a
statement-protocol label when their own prompt contract, audit/item digests,
locators, classifications, and reasons remain current.

Treat a source-record contract upgrade separately from an ordinary differential
revalidation. An exact descriptor mismatch caused by newly generated Lean
field-slot, type, graph, or execution receipts is fail-closed by design; do
not add those fields to a generic ignore list or rewrite old aggregate hashes.
New groups and changed group topology are current review work. A future
additive-evidence transport may operate only through a separately versioned
bridge that pins immutable historical inputs and source/toolchain context,
matches a name-independent legacy core uniquely at equal topology, recomputes
every added receipt under the exact current audit scope, revalidates the
current source route, and rejects unknown additions or ambiguity. Until that
bridge exists and independently validates, schedule one frozen raw reissue
after interface/map changes settle rather than retrying identity-only gates.

For the paper-local generated-status boundary, run:

```bash
python3 scripts/sync_paper_status.py --paper <paper-folder>
python3 scripts/sync_paper_status.py --paper <paper-folder> --check
```

This reads and writes only paper-owned README/legacy-note output and validates
local status shape/routes/counts. It does not traverse other papers or claim
that aggregate JSON, Markdown, or the site is current. The strict closeout reads
paper-local `status.json`, so aggregate drift is not a theorem/provenance
closeout blocker. Reserve unscoped status sync and dashboard audit for an
explicit integration or release refresh. After a consolidated zero-error
closeout, do not rerun individual dashboard lanes unless diagnosing a named
failure.

Use the cheap-to-expensive ladder only during active remediation or after a
named failing lane. After Lean edits, run the focused build and the named
provenance diagnostic. Then run only affected row-local statement,
source-to-Lean, coverage, and assumption prechecks. Regenerate the recursive
source-record artifact only after that source/review surface is stable. Refresh
the final-report summary and generated status tables next, and run the
repository closeout gate once at the end. Stop and fix the first stale or
semantic failure instead of repeatedly rebuilding every later layer. A passing
repository gate for a paper with partial status proves audit consistency only;
it does not discharge the explicit source-proof queue.
At a frozen closeout entry, skip this manual ladder: the planner is the first
command and schedules any required build, manifest, or strict work.

For a paper that remains `partially formalized`, the targeted
`--paper-closeout` command intentionally exits nonzero for the declared
source-target queue. Treat it as a queue-reconciliation check: its output must
contain only those documented source-map and coverage findings. A stale status
count, unconfigured review declaration, source-record failure, hidden premise,
or sidecar error is separate audit debt. Do not run
`audit_repository.py --paper <paper> --include-active` without
`--paper-closeout` as a substitute: it also evaluates repository-wide hygiene
and obscures the target-paper result.

Before that expensive reconciliation, run `sync_paper_status.py --paper
<paper> --check` after the one paper-local render. Keep
`paper_interface.line_count`, review-surface classification, and
`human_review.total_rows` in the local status file current so the closeout gate
is not spent rediscovering deterministic metadata drift. Do not run a five-minute
all-paper status check as a prerequisite for a paper-local semantic closeout.

An acknowledged proof component is not a source-facing theorem. Remove it from
`include_names`, place it in `auxiliary_names`, and keep the complete source
claim in the source inventory as `partially_covered`. Route the component only
through `support_lean_declarations` and coverage `support_declarations`; do not
leave it in aliases or direct declaration routes. This preserves the useful
building block while preventing its certificates, support facts, or optimality
facts from being audited as accepted source assumptions.

After the final review-surface change, regenerate `source_record_audit.json`
and update `source_record_match_llm.json` only from its exact required keys.
Every retained judgment must carry the current audit digest and current
per-item digest; prune judgments now covered by a direct, current statement
ledger. A partial source-proof queue is expected only when it is the exact
documented queue. Stale/missing source-record judgments, hidden premise
findings, or components that still leak into the review surface are separate
audit failures.

### Differential Revalidation And Strict-Cost Control

A differential source-record overlay is bound to one exact prior raw audit,
its prior judgments, and one exact current raw audit. When any of those
identities or an item descriptor changes, regenerate the overlay from a
compatible archived pair or treat every overlay-covered item as stale. Never
repair freshness by copying aggregate hashes or timestamps, or by using reuse
exclusions to suppress a stale item. Before spending a final closeout, run the
cheap current-judgment preflight: the authenticated union of direct judgments,
Lean-owned runtime receipts, and differential items must cover every current
required group exactly once.

Manual/template coverage generation is a diagnostic or planning path, not an
ordinary closeout companion and never an acceptance credential. In a frozen
closeout transaction, expensive manifest, type-certificate, and terminal-shape
work may be shared only under an exact content identity: raw inputs, Lean
closure/helper, protocol, and mutation boundary. A persisted cache may schedule
work but cannot certify it; strict acceptance still validates current bindings
and the final mutation boundary.

Do not label a machine raw refresh or a strict source-to-Spec closure-hash
refresh as a human receipt reissue. Before materializing a statement-receipt
plan, count semantic deltas: zero fresh targets and zero retirements means the
existing judgment bodies already cover the current surface and the operation is
a no-op. Do not create an archive, scaffold, or replacement sidecar for that
case. A storage-only rewrite needs an explicit, separately recorded migration;
it is not evidence of a new audit.

When the statement-audit protocol changes, first revalidate the complete
statement ledger, including every newly required `semantic_scope_review`
dimension, then regenerate the source-record artifact once. Updating only the
prompt label makes the direct statement ledger fail closed and creates
duplicate source-record work without new semantic evidence.

If the cheap identity gate reports that a legacy raw source-record receipt has
no current Lean import-closure receipt, treat that as one scheduled transport
repair, not as a reason to retry the gate. First finish every map, route,
source-anchor, and existing-sidecar change for that paper. Before launching
the one full scan, archive the canonical raw receipt and its judgment sidecar
as an exact pair. The present producer writes a requested noncanonical
`--out` transport copy for inspection, but a successful full scan also
atomically refreshes canonical raw evidence; `--out` is not a delayed
promotion mode. Inspect that copy and the refreshed canonical artifact after
the one run. A changed or unreusable semantic item is a real targeted review
obligation; otherwise refresh only the judgment summary after any sidecar
edit. Do not re-run the Lean-backed raw generator once for each administrative
map field.

Freeze the raw producer and every direct semantic helper before beginning the
serialized scan. In particular, finish and validate shared audit-engine,
closure-runner, source-map, and review-surface edits before the transaction;
do not edit those inputs while it is running. If the final input fingerprint
reports a mid-scan mutation, the completed candidate has no evidence credit:
record the operational invalidation, finish the shared changes, and schedule
one replacement transaction from the frozen state rather than trying to patch
or relabel the candidate.

Do not run the final cache rebuild and the recursive source-record audit in
parallel in a shared worktree. Run focused Lean builds during proof edits, then
serialize those two manifest consumers and the final prechecks.

Use `documented additional assumption` only for a premise that is either
explicit in the source or is a deliberately stated caveat. A missing source
conclusion, optimizer, uniqueness fact, or formula is a source-target gap, not
a conditional boundary and not a premise to package in a certificate record.

## Final Validation Report

`FINAL_VALIDATION_REPORT.md` is a concise human assessment, not a handoff note,
implementation ledger, shell transcript, or closure receipt. It must put an
`Updated: YYYY-MM-DD` line directly below the H1 title, using the date of the
report's latest substantive refresh. It must answer five questions near the top:

The authoritative scaffold is
[`../../../papers/TEMPLATE/FINAL_VALIDATION_REPORT.md`](../../../papers/TEMPLATE/FINAL_VALIDATION_REPORT.md).
`scripts/new_paper.py` reads that file directly; do not maintain a second
embedded report template.

- What was proved?
- Did formalization find anything wrong or ambiguous in the paper?
- Was any qualitatively different proof/modeling route needed?
- What remains for Lean proof work versus human dashboard review?
- What generalizations, conjectures, or extensions look trivial or
  near-trivial after formalization?

Write in paper language, not Lean-internal implementation language. Avoid
history markers such as `previously`, `now`, `restored`, or `superseded`
unless the historical comparison is itself a source-paper caveat or requested
retrospective.

### Human-facing front-matter boundary

Treat Sections 1--11 as the report's executive, paper-facing assessment.
They answer what the paper proves, whether the paper has a real issue, and
what mathematical work remains. They are not a compressed audit trace.

Before saving a report, remove from Sections 1--11:

- Lean declaration/module/file names, representation choices, helper
  constructions, state machines, certificate or interface plumbing;
- source-file hashes, transcript/rendering procedures, command lines, build
  diagnostics, audit-row counts, and validator inventory; and
- prior implementation defects, refactor/remediation chronology, or a resolved
  proof-route comparison that does not change the paper's mathematics.

Put verifiable technical material in public audit JSON or the canonical closure
ledger. `FINAL_VALIDATION_REPORT.md` ends at Section 11. Do not use its
human-facing sections to explain a resolved internal issue or to say that former
gaps, defects, or remediation are no longer caveats; state only the current
mathematical disposition.
For a fully formalized paper with no genuine gap, additional assumption,
material proof-strategy departure, or caveat, Sections 5--7 and 11 should read
`None.`. A source-level condition or a formalization convention that preserves
the paper's endpoint is neither an additional assumption nor a caveat.

Use **clarification** for an intended source-model condition, convention, or
interpretation that is made explicit. Reserve **correction**, **corrected**,
and **repair** for a demonstrable false source formula, statement, or proof
step, or for an explicitly approved replacement target. Do not call an
otherwise source-consistent clarification a correction merely because it is
spelled out in the formalization.

Use this section order:

1. Human Verdict
2. Closeout Status
3. Source and Scope
4. Researcher Summary of Checked Results
5. Remaining Boundaries and Gaps
6. Additional Assumptions Beyond Paper
7. Proof-Strategy Deviations
8. Proof Tricks Worth Reusing
9. Generalizations, Conjectures, and Extensions
10. Source Clarifications and Exact Readings
11. Paper Issues or Caveats

Store row-level validation, source coverage, assumption provenance, and tool
receipts in the public audit JSON and canonical closure receipt. Do not leave
placeholders or pointer prose; fill each report section with a concise
paper-facing conclusion, even if that content is `None`.

Use Section 10 for a material source clarification or, only when necessary, a
demonstrably false printed formula or statement. State its present mathematical
reading and theorem-level effect without narrating an earlier repair. Section 11
should say there is no paper-level caveat when that clarification does not
change the formalized endpoint or add a non-source assumption.

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
- Interpret that status as the mathematical coverage classification, not as a
  substitute for the current `FINAL_CLOSURE_RECEIPT.md`. A current closure
  receipt is required before claiming closeout completion or release readiness.
- One-sentence recap that does not repeat the full human verdict.
- Human review status, without treating that governance state as proof debt.

Put Lean footprint, row counts, source hashes, and detailed audit/validator
totals in public audit JSON and the canonical closure receipt. They are useful
evidence, but not a reader-facing description of the mathematical result.

### Researcher Summary of Checked Results

Keep this short: normally 3-6 paper-language bullets, one per major source
definition/result cluster. If it starts listing subclaims, helper formulas, row
counts, source-record packages, state transitions, or implementation route
details, move that material to the public audit JSON.

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
provenance, or theorem statements. Do not list finite-type infrastructure,
numeric encodings, data representations, or harmless formalization conventions.
If none exists, write `None.`.

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
proof-organization notes here. Do not explain a resolved prior Lean defect
here or elsewhere in the front matter. Put technical material in `Detailed
Formalization Evidence` or the relevant audit sidecar instead. If the only
differences are explicit formalization boundaries, write
`None.`.

### Generalizations, Conjectures, and Extensions

After the main source claims are closed or clearly bounded, do one fresh
outside-Lean thinking pass over the final proof route. Record what looks
trivial or near-trivial to generalize, prove as a conjecture, or extend:

- weakened assumptions or parameters that the proof no longer uses,
- immediate corollaries or stronger conclusions already implicit in the Lean
  proof,
- source conjectures or natural adjacent conjectures that the current library
  can now prove cheaply, and
- extension ideas that are plausible but nontrivial and should stay future work.

Write `None` if there are no such opportunities. Do not count an optional
extension as paper coverage, a proof-strategy deviation, or a remaining gap
unless the source paper itself claims it. If a cheap extension is proved, state
that it is beyond the paper and name the paper-facing or library declaration
where it lives.

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

Every displayed or source-defining formula used by a selected named result must
be checked in that result's transparent realization path. An exact helper or
subclaim row may make the dependency legible, but a standalone display is not
an independent normal-scope item unless it is itself source-presented named
theory. Any formula row used as evidence is closed only when derived in Lean
from source primitives or separately validated paper assumptions.

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
counts by hand. The narrative must distinguish receipt-authorized evidence from
tracked metadata whose freshness was not established by that receipt.

### Paper-Facing Statement Validator Ledger

Present the reviewed paper statements in source language, with Lean declaration
names serving only as navigation. Translate machine classifications into the
human labels defined by the report template; raw enum values belong in JSON,
not in the public narrative.

### Source-Coverage Audit Ledger

Summarize the independently curated source inventory and its disposition, then
list the selected named-theory items and their reviewed Lean routes. Keep
figures, captions, empirical results, simulations, numerical examples, and
other non-named prose outside normal named-theory scope. A deep-paper audit may
list them separately, but it must not make the ordinary report unreadable.
Machine digests and item-level diagnostic history stay in the audit sidecars.

## DAG and Source-JSON Audit

The DAG is a human-readable proof roadmap over the source inventory, not a
Lean implementation changelog. Before closeout, compare:

- the source paper and source-block inventory,
- `audit/paper_statement_map.json`,
- `paper_coverage_llm.json`,
- `PaperInterface.lean` / dashboard rows,
- `docs/DependencyDAG.tex`, and
- the rendered `docs/DependencyDAG.pdf`.

Every selected normal-mode source item should be represented by a visible DAG
node, unless the final report gives an explicit source-facing reason for
omission. This includes independently source-presented named definitions,
results, theorem-like claims, assumptions/model conditions, and named appendix
theory. Standalone formulas, equations, and algorithms are independent DAG
inventory only in deep mode; in normal mode, show them inside a selected named
result's dependency node when that context is useful. A scope note alone must
never be the only place a selected source item appears. Named open problems may
appear as explicit nonproof nodes rather than theorem nodes.

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
nodes. Do not make an implementation-proof route visible merely because it was
needed in Lean; use a node only for a source-presented named lemma/result or a
genuine paper-level model dependency. Group source definitions with the result
cluster they define when they have no independent source-to-result edge. Put
technical proof details in proof notes or audit ledgers.

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
- current source-relevant proof-organization facts, and
- command transcripts or diagnostic notes.

Keep `FINAL_VALIDATION_REPORT.md` concise. Include audit-note material in the
human report only when it changes the theorem statement, requires an additional
assumption, identifies a source-paper issue, or explains a real remaining
boundary. Do not use either report as a project-history archive: omit retired
proof layers, rejected approaches, and other implementation chronology unless
the comparison itself is a source-paper caveat or an explicitly requested
retrospective. Put genuinely useful implementation history in a private handoff
or commit message instead.

## Notes vs. Gaps vs. Deviations

Use these classifications consistently:

- **Gap / remaining boundary:** a theorem-level mathematical, library,
  analytic, runtime, solver, external theorem, source-model, or certificate
  boundary that remains undischarged for a claimed paper result.
- **Additional assumption:** a non-source condition that the Lean theorem needs
  beyond the paper, if the human has approved or the report is explicitly
  marking it as beyond-paper. A central endpoint depending on it remains
  `partially formalized`; human approval does not turn it into a caveated full
  formalization.
- **Source condition:** a parameter, model primitive, algorithm condition, or
  conditional theorem hypothesis stated by the paper. This is not a gap,
  deviation, or additional assumption merely because Lean exposes it.
- **Proof-strategy deviation:** a substantive mathematical difference between
  the source proof route and the Lean proof route. It must name both routes.
- **Source note / proof-organization note:** information useful for readers or
  future agents that does not change the theorem statement and is not proof
  debt. Put it in source/scope, detailed evidence, proof tricks, or audit notes.
  This includes corrected printed-proof steps, typos, minor constant/sign
  corrections, routine implicit conditions, repaired auxiliary lemmas, or
  alternative proofs when Lean proves the same substantive advertised endpoint
  from source primitives. Record ledger defects as
  `status_impact: formalized_note`.
- **Paper issue or caveat:** a substantial error in a central source-paper
  claim that materially changes what the paper can claim, with a corrected
  endpoint fully proved in Lean. Record it as
  `status_impact: formalized_with_caveat`. Do not use this label for a minor
  source repair, proof-only repair, non-source additional assumption, or
  incomplete/weaker Lean target.

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
- "One paper reuses another paper's checked support route" is a downstream
  reuse/proof-organization note unless the source proof route is substantively
  different and the report explains both routes.

## Public PR Closeout

Before a public PR, confirm the target public checkout has the paper-local
status, DAG source/rendered PDF, final report, source-audit note, LLM sidecars,
and generated status surfaces in sync. Stage explicit path lists only. Do not
copy private source PDFs/text caches or unpublished paper folders into public.
