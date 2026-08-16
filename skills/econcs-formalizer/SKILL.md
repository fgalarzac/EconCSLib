---
name: econcs-formalizer
description: Formalize economics-and-computation papers in Lean. Use for source inventories, source-faithful paper interfaces, formalization planning and coordination, semantic audit and reuse, reusable-library extraction, paper closeout, and private-to-public preparation. Pair with econcs-prover for active Lean proof construction and repair.
---

# EconCS Formalizer

Turn paper claims into source-faithful Lean statements, checked proofs, and
auditable closeouts. Use `skills/econcs-prover/SKILL.md` for the inner Lean
proof/error loop.

## Normative Protocol

Read `config/formalization_audit_protocol.json` before changing scope, audit
versions, reuse, status classification, build selection, or campaign pacing.
It is the normative machine-readable policy. This skill and workflow docs
defer to it whenever prose conflicts. Validate it with:

```bash
python3 scripts/formalization_protocol.py
```

The essential current distinctions are:

- statement semantic review and recursive source-record audit are v10 lanes;
- theorem-realization correspondence is v11 for new papers and explicit v11
  upgrades; a legacy material repair instead needs current item-level v10
  source and Lean evidence, never a relabelled v11 receipt;
- normal scope covers independently source-presented named theory;
- standalone formulas, equations, algorithms, figures, captions, examples,
  simulations, empirical claims, and computational results are deep-only;
- audit reuse is item-level and depends on the full transitive elaborated
  semantic dependency plus opaque imported-terminal artifacts, never names;
- within one audit process, successful compact Lean revalidation receipts may
  be shared only under the same complete compiled-context coordinate; never
  persist, infer, or cache a failed/missing receipt, and never treat a
  declaration name as the reuse authority;
- source-row/`PaperInterface` associations use exact semantic bindings, never
  positional pairing or Lean-synthesized source meaning;
- transparent `Spec` declarations support comparison and routing but receive no
  proof credit without the reviewed theorem's closed proof;
- proof work comes first; routine documentation waits for material boundaries;
- close a paper with its full paper-root build, owned by the consolidated
  closeout; run a separate build first only when the reuse planner schedules it.

When a source-record scan owns the repository lease, inspect its bounded phase
metadata rather than guessing from shared temporary scripts. It is operational
diagnostics only and cannot justify a raw reuse, reissue, or closeout result.

## Repository Rules

- Work in `EconCSLib-private` on `main` unless the user explicitly requests a
  branch. Do not edit, commit, push, or serve the public repository unless the
  user explicitly asks.
- Treat a dirty worktree as shared. Read diffs before editing, preserve other
  agents' work, and coordinate paper ownership in the current coordination
  file. Do not work on a paper assigned to another agent.
- Treat every existing `human_summary`, public-note, website-table note, and
  paper-table comment as user-authored public copy, including text recovered
  from the active public checkout. Never replace, expand, paraphrase, or
  remove it because a formalization or audit changed; do so only on the user's
  explicit instruction for that prose. Before regenerating public status,
  compare the paper-local summary with the prior public surface and preserve
  the prior text unless the user has directed a change or it is demonstrably
  no longer true. Put audit detail in the report or sidecars, not the note.
- For a partial-paper public note, use two short parts: what paper-facing
  result or scope is formalized, then the external clarification, assumption,
  data, or proof needed to finish. Do not put internal audit process, broad
  proof history, or implementation detail in the note.
- For `FINAL_VALIDATION_REPORT.md`, keep Sections 1--11 as human-facing paper
  assessment. State only the paper result, actual theorem-level boundary,
  genuine beyond-paper assumption, material source-proof departure, or
  status-bearing caveat. Do not put Lean names, file paths, representations,
  helper constructions, audit counts, source hashes, command output, or prior
  implementation history there. Do not explain that a former gap, defect, or
  remediation was resolved: state only the current mathematical disposition.
  Put technical evidence only in public audit JSON and closure-ledger sidecars;
  reports end at Section 11. Write `None.`
  for an empty assumptions, deviations, gaps, or caveats section rather than
  converting a resolved implementation detail into a public note.
- Keep the Human Verdict to the present paper-level disposition, covered
  result family, and review state. Do not use it for source conventions,
  correction history, proof machinery, or an implementation inventory. A
  source-faithful representation or convention is not an additional assumption
  or proof-strategy deviation: use `None.` in Sections 6--7 unless there is a
  real mathematical premise beyond the source or a material departure from its
  proof.
- If Section 10 records a source typo or clarification, either state the
  before-and-after mathematics precisely there or link to a concise,
  paper-local `docs/SOURCE_CLARIFICATIONS.md`. That note must give the pinned
  source anchor, corrected or clarified reading, and result-level effect; it
  must not substitute Lean history, declaration inventories, or audit process
  for mathematical detail. When linking out, retain a one- or two-sentence
  mathematical summary in the report; never replace the report's explanation
  with a link alone. A source-clarification note may keep a legacy filename,
  but its current content must be source-facing only: remove closeout history,
  commands, implementation routes, and Lean declaration inventories. Prefer
  “clarification” unless the printed formula or statement is actually false.
- Preserve a genuine source-proof deviation during report normalization. State
  its source route, the material underspecification or departure, the checked
  paper-level route, and whether the theorem statement changes. Do not delete
  it merely because it is not a paper-level caveat; link a concise paper-local
  note when more than a short report summary is needed.
- The website's **Human review** column must render the saved human
  `reviewed_rows/total_rows` count only. Translation freshness, stale-machine
  evidence, mismatches, and uncertainty belong in audit artifacts, never in
  that public-facing review-count column.
- When a user maintains a paper or website feedback `.txt` file, preserve every
  user note verbatim. After the requested edit is complete and its relevant
  validation has passed, append `done. [brief outcome]` immediately after that
  feedback item; never mark an item done merely because it has been inspected
  or queued.
- In a `DependencyDAG`, show source-presented definitions, models, named
  results, and genuine paper-level dependencies. Do not show Lean proof
  support, implementation helpers, declaration names, or remediation history
  unless a source-presented named lemma itself warrants a node. A source
  definition without a direct theorem edge may still appear, but group it with
  its source-result cluster rather than giving a separate implementation path.
- Proceed one paper at a time. Record a paper transition when ownership or the
  active paper changes; prefer one commit and push after each finished paper
  when requested.
- Every paper has `PaperInterface.lean`. It is the human and machine source
  review surface, even if proofs and audit helpers live in imported modules.
- Do not rename or delete legacy audit-facing files during a proof campaign
  unless that cleanup is the assigned task. Record neutral-name cleanup for a
  separate boundary.
- For public/private export and history safety, read
  `skills/econcs-formalizer/references/public-private-sync.md`. Do not push a
  private commit graph directly to public.

## Start Or Resume A Paper

For a new contributor-owned paper, enter through
`python3 scripts/paper_contribution.py new ...`, not the lower-level
`new_paper.py` generator. The facade requires complete intake metadata,
registers the focused Lake target atomically, and preserves the one-paper pull
request boundary. Use `paper_contribution.py check <paper> --fast` during proof
work and its full check at the source-present closeout boundary. Aggregate
status/docs/site generation belongs to the mechanical aggregate-only follow-up
and must not be added to a one-paper pull request.

1. Read the current source artifact, `status.json`, `PaperInterface.lean`,
   paper-local audit map, validation report, coordination row, and recent diff.
2. Confirm the exact source version and byte-pinned text/TeX artifact. Existing
   local source caches take precedence over repeated web retrieval.
   If the source arrives as a TeX or text archive, do not treat an unpacked
   working copy as an alternate canonical artifact. Build a deterministic,
   paper-local text surface from explicitly named, byte-pinned archive members,
   record the archive-member provenance in `source_archive_surface`, and put
   every map anchor on that derived surface. The archive, each selected member,
   and generated surface must reconstruct one another exactly. A public
   candidate may retain the provenance record but never the source bytes. In a
   public structural checkout, missing licensed source bytes mean only that
   source content cannot be rechecked there: preserve the pinned provenance and
   final closure receipt, report that limitation as structural/non-certifying,
   and do **not** call the private source review stale or demand reissue solely
   because those bytes are absent. Reissue requires a material source, map,
   interface, proof, or protocol change verified in the private checkout.
3. Build a source-only inventory of named definitions, assumptions/model
   conditions, lemmas, propositions, theorems, corollaries, and visibly named
   theorem-like claims. Map keys and Lean names are navigation only.
4. Check each selected statement outside Lean for domains, quantifiers,
   premise/conclusion direction, constants, signs, normalization, nonvacuity,
   uniqueness, timing, information, equilibrium refinements, and dependencies.
5. Search Mathlib, Cslib, Optlib, `EconCSLib`, and existing paper modules before
   creating a new mathematical abstraction.
6. Write the exact audited paper-facing propositions in
   `PaperInterface.lean`. It is acceptable and preferred to begin with `sorry`
   proofs once each statement itself is source-correct and its assumptions are
   visible. This produces a trustworthy proof-obligation queue.
7. Freeze intake before proving: verify the complete normal-scope inventory,
   byte anchors, source premise/conclusion atoms, exact `Spec` types, dependency
   order, and owning module/agent for every obligation. Run one focused
   manifest and semantic statement review on that stable skeleton. The
   underlying scaffold intentionally does not create a dashboard cache; create it
   once only after this freeze. During that fully current initial review, run
   `semantic_audit_reuse.py --bootstrap-current --write` once to seal the
   entry-local semantic identities needed for later item-level reuse. This is
   metadata creation, not a stale-evidence override. A proof-body replacement
   then preserves the statement judgment when its type and semantic dependency
   identity are unchanged.
   Newly scaffolded papers record this boundary in
   `audit/intake_freeze.json`; seal its exact source byte slices, total
   dependency order, owners, and acceptance conditions before closeout.
   A trusted pre-rollout commit defines the legacy cohort. Existing cohort
   papers without that prospective marker remain `legacy_not_configured`: do
   not backfill it, reopen them, or rerun audits. Marker removal from a new
   paper is an intake failure, not a downgrade to legacy.
8. Choose the first dependency-ordered proof seam and prove it. Update plans or
   reports only when the source target changes or a handoff is needed.

Use `templates/FORMALIZATION_PLAN.md` when a new plan is necessary. Do not
recreate a plan merely because an up-to-date one exists.

## Source Scope

Normal `named_theoretical_statements` mode requires:

- named theorems, propositions, lemmas, corollaries, and definitions;
- source-labelled theorem-like claims;
- explicitly named assumptions, conditions, or governing models needed by the
  selected results;
- named appendix theory.

Do not create independent normal-scope obligations for standalone equations,
formulas, algorithms, numerical examples, figures, captions, tables,
simulations, empirical observations, or implementation measurements. Inspect
such material when it defines or supports a selected named theorem. Use
`deep_paper_with_all_prose_claims` only when explicitly requested; it requires
its own source-pinned completeness attestation.

An inventory must be source-only and complete independently of the map being
audited. Unknown named presentations fail closed. Repeated source
presentations stay byte-pinned but may be linked to one canonical claim through
the explicit source-presentation alias protocol. Explicitly inventory every
definition-shaped prose presentation, even when the resulting list is empty.
Give each one a source-only scope disposition; retain local notation and
computational/deep-only definitions with content-pinned independent scope
judgments rather than silently dropping them. A catch-all deep-only exclusion
also needs explicit user approval. A canonical normal definition binds to a
map statement only through a current semantic-equivalence receipt pinning both
sides.

## Statement Fidelity

Paper credit comes from source semantics, expanded Lean propositions, and
proof closure. Never infer fidelity from declaration, field, binder, function,
record, or map-key names.

- Put every material premise and conclusion in the elaborated
  `PaperInterface.lean` type or a transparent audited `Spec : Prop`.
- Do not hide conclusions in caller-supplied certificates, records, witnesses,
  runs, equilibria, selectors, convergence packages, or source-row equations.
- Distinguish conditional behavior from existence, nonvacuity, uniqueness,
  positive mass, termination, feasibility, and optimality.
- For algorithms, audit the executable transition semantics, tie-breaking,
  terminal outcomes, and complexity claim through the transitive closure.
- For equilibrium and strategic claims, state action spaces, timing,
  information, beliefs/PBOs, payoffs, off-path/null behavior, and refinement.
  A selected or one-sided deviation check is not a whole-equilibrium proof.
- For measure-theoretic statements, make pointwise versus almost-everywhere
  conclusions and null-set conventions explicit. Do not spend a long campaign
  on harmless zero-mass conventions when the user has approved the source
  convention; record the interpretation.
- Use a proven library for established voting, optimization, matching, or
  algorithmic semantics when available. Do not replace an existing executable
  STV/RCV model with an ad hoc paper-local surrogate.

The semantic audit must traverse elaborated expressions, implicit arguments,
typeclass inputs, conjunctions/iff/implications, transparent definitions,
record fields, constructors, and imported dependencies. Syntactic token scans
and name-pattern detectors are diagnostics only.

Treat each claimed source-row/`PaperInterface` association as an exact semantic
binding. Ordered arrays are presentation only: never zip rows by position, and
never repair missing source semantics by copying a Lean type, binder, or
statement. Explicit one-to-many coverage must be represented explicitly. A
transparent `Spec : Prop` may mediate direct structural comparison and route
selection, but only the reviewed theorem's elaborated type and closed proof can
earn theorem proof credit.

For a `Spec`/proof contract, Lean Meta must establish exact elaborated
proposition equivalence and traverse the paper-local transparent dependency
graph. Python may validate artifact pins and display diagnostics, but it must
not recursively normalize binders or expression trees to grant semantic proof
credit. Batch these Lean checks per review module and reuse the artifact-pinned
verdict for every downstream consumer.

For a global algorithmic claim, audit the exact input domain, state transition,
terminal outcomes, termination, and numeric representation. Require coherent
joint witnesses, nonempty valid families, and surjectivity where syntax is
claimed to represent the semantic domain. A local/refinement theorem needs a
checked global bridge before it can establish the advertised endpoint.

For a runtime claim, inspect the executable's transitive semantic operational
dependency graph across every branch reachable over the claimed input domain.
Show that no reachable branch still evaluates an old semantic closure or oracle;
function and declaration names are routing only. When eliminating closure work
is material, require a cost-threaded executor or generated IR/C evidence pinned
by source and artifact digests to the audited build, plus a worst-case recurrence
that charges traversal, duplication, rebuilding, representation, and arithmetic
bit growth.

## Corrections And Assumptions

Apply the categories in the normative protocol:

- An implicit source condition or equilibrium refinement made explicit is a
  formalization note when it expresses the paper's model. Call it a
  **clarification** in human-facing prose, not a correction. Record it in the
  theorem statement and post-formalization report; it is not automatically a
  caveat or extra assumption.
- Reserve **correction**, **corrected**, and **repair** for a demonstrable
  false source formula, statement, or proof step, or for an explicitly approved
  replacement target. Do not use those words merely because the formalization
  makes an intended model condition or convention explicit.
- A genuine non-source condition is an additional assumption. Keep it visible
  in Lean and the report and never attribute it silently to the paper; the
  original source endpoint remains partial.
- A minor typo, equality/inequality convention, appendix slip, or proof repair
  that preserves the advertised endpoint is a `formalized_note`, not a caveat.
- A substantive corrected target needs explicit approval, defect IDs, pinned
  archival and corrected statements, and `archival_equivalence_claimed: false`.
- “Formalized with caveat” is reserved for a material accepted boundary, not a
  difference of opinion, routine regularity, null-region convention, typo, or
  proof-strategy repair.

When `=` versus `<=`/`>=`, strict versus weak, or a similar source convention is
ambiguous, ask the user if available. Otherwise make the truth-preserving
condition visible, record it, continue actionable proof work, and raise it at
the next interaction.

## Proof Campaign Pace

After the statement and visible premises are audited, prioritize mathematical
obligations. Do not interrupt an actionable proof campaign for broad audit-code
expansion, rendered DAGs, status prose, repeated semantic extraction, or
whole-paper regeneration.

Update documentation at these boundaries only:

- material source-scope or source-version change;
- assumption/correction decision;
- meaningful proof boundary or blocker;
- handoff or paper transition;
- paper closeout.

At a blocker, leave the strongest compiling paper-facing statement with
`sorry`, exact source anchors, dependency order, forbidden shortcuts,
acceptance conditions, and a copy-paste assignment prompt. This is more useful
to a less capable model than a narrative progress log.

## Semantic Audit Reuse

Reuse completed review per item when every identity required by
`config/formalization_audit_protocol.json` is unchanged. In particular, pin:

- normalized source semantics and current byte-validated quote;
- the elaborated Lean signature, with raw declaration spelling retained only
  as trace evidence after a unique semantic match;
- transitive elaborated semantic dependency graph, including imported
  definition bodies reached by the reviewed statement;
- exact artifacts for opaque imported terminals whose bodies are unavailable
  to the graph, package/toolchain context, and audit generator/validator
  identities;
- configured route preflight and correction/convention dispositions.

Names and source coordinates may locate candidates but never establish
identity. A navigation-only move can rebind only after current byte validation
and a unique semantic match. Missing, changed, ambiguous, or unresolved
identity reopens that item. Do not rerun unchanged items or whole-paper
extraction solely because unrelated source, documentation, or audit items
changed. Whole review-module artifacts and theorem proof bodies are not
statement-semantic identities; replacing `sorry` with a proof preserves an
unchanged statement judgment while reopening proof-closure evidence.

Lean owns both semantic dependency reachability and repository import routing;
Python consumers validate the emitted graphs and their byte identities rather
than reconstructing either graph from names or import text. Carry unchanged
saved status only through an immutable receipt binding the exact import closure,
canonical source attestation, statement/coverage dispositions and counts, and
name-free semantic source bindings. A cache-free checkout may validate that
receipt from tracked inputs; missing or ambiguous bindings reopen the item.

Canonical audits use only the exact import closure rooted at the configured
`PaperInterface.lean`. Ambient scratch, untracked, and unimported `.lean` files
may be reported as hygiene diagnostics but must not change canonical receipts.
Acquire status, maps, sidecars, Lean sources, source text, companions, and PDFs
once into the closeout's immutable input bundle. Parse large JSON once and pass
the exact byte mapping to every validator; a strict consumer must not fall back
to a live read. Prompt wording and report rendering are presentation inputs and
must not invalidate the semantic raw producer.

## Build And Closeout

Keep workflow and semantic-producer changes in separate commits. A planning,
process-recovery, status-rendering, or documentation improvement must not bump
prompt/protocol/schema/producer identities, rewrite tracked paper evidence, or
force current papers through another audit. If a change genuinely alters a
generated semantic obligation, identify its affected papers through semantic
features, land it separately, and reopen only that set. Never hide such a
producer change inside a closeout-speed patch.

During proof iteration:

```bash
lake build <PaperRoot>.PaperInterface
```

### Closeout Cost Decision

Before any expensive closeout work, freeze the paper inputs and make one
explicit choice among these evidence paths:

1. **Exact item-level reuse** when the source anchor, expanded paper-facing
   declaration, transitive Lean closure, and applicable source-model context
   are unchanged. Reuse is a semantic identity decision, never a declaration
   name or a matching filename.
2. **One focused regeneration** when current evidence is stale and a fresh
   paper-local run is cheaper, clearer, or less risky than reconstructing a
   chain of historical receipts. Prefer this to hand-rebinding old sidecars or
   repeatedly investigating archival execution state.
3. **Direct source-row review** only when the user selects that mode or the
   protocol permits it. Review every normal-scope row against its pinned source
   anchor and current expanded `PaperInterface` endpoint, including domains,
   premises, quantifiers, and terminal conclusion. Record the row ledger and
   mark old machine receipts historical; never relabel them as current.

For every completed closeout, create or refresh exactly one canonical
`FINAL_CLOSURE_RECEIPT.md` at the paper root. It is the sole paper-local answer
to “is this paper currently closed?” It records the selected evidence lane, the
pinned source/map/interface-closure/reviewer-ledger identities, focused-build
result, protocol identity, and the frozen commit. A raw source-record artifact,
a direct-review ledger, a planner-worker record, and
`FINAL_VALIDATION_REPORT.md` are evidence inputs or a mathematical summary;
none is a competing final receipt. Use the template and exact refresh rules in
`references/final-closure-receipt.md`.

Refresh this receipt only after a material input to its selected lane changes:
the source artifact or route, statement map, import closure, selected reviewer
ledger, evidence-lane semantics, or focused build target. A
`review_compatible` audit-engine transition, aggregate-status rendering, report
prose, and operational trace change do not by themselves reopen it. When the
receipt records `direct-source-row-review`, do not manufacture a raw reissue
solely because an old raw receipt is historical; instead revalidate the direct
ledger and all receipt-bound identities. Do not switch evidence lanes merely
because the first path emits a legacy-receipt warning. If a recovery sequence is
longer or less certain than a single focused regeneration, regenerate once
instead. If neither route is authorized or technically sound, stop and name the
missing evidence rather than creating scaffolds, attestation fragments, or a
second recovery attempt.

During one closeout, run each unchanged expensive lane at most once. After a
failure, repair the specific invalid item or source/interface mismatch, then
continue with the one planned successor. Do not repeatedly run the planner,
dashboard, aggregate status generation, full repository build, source scan, or
receipt recovery against unchanged inputs. Paper-local status checks and the
focused paper build are the default boundary checks; aggregate generation is an
integration or release task.

At the start of closeout, freeze edits and plan exact reuse before launching an
expensive gate:

```bash
python3 scripts/closeout_reuse_plan.py --paper <PaperRoot>
```

This is a state machine: execute only `next_action`, never batch the explanatory
`actions` list; run an `after_*` action only after its named predecessor; replan
only when explicitly instructed; and stop on every `inspect_*` action. Finish
all tracked paper/report/DAG/status edits before planning. A material failure
returns to repair and one new frozen plan; do not edit tracked paper files after
a pass.

The planner uses the same component inventories, canonical coverage selection,
source-map/surface identities, direct-expression policy, and validator
identities as the semantic reuse tool. It reports new and retired obligations
explicitly. Its ignored advisory cache is scheduling data, never evidence. An
unchanged repeated plan reuses that projection. Exact compiled byte identities
are durable; integrity-bound stat guards only avoid rereading unchanged files.
A changed repository guard hashes that path; changed external guards refresh
their exact aggregate. An identical-byte rebuild preserves the plan while
changed bytes replan. Strict closeout still validates exact bytes.

The default output omits successful item receipts and retains every repair
obligation. Use `--all-items` only when the complete reusable-item inventory is
actually needed.
Execute the printed `next_action`. When a cache-miss build has a
state-qualified manifest-refresh successor, continue through that successor
and its explicit replan boundary from the same frozen plan; do not rerun the
planner between those two steps. A rebuilt artifact always replans before
strict closeout. If an existing audited paper predates entry-local reuse pins,
the planner may
validate those items in memory for the current closeout but must not rewrite the
paper or require another audit. Seal the pins at that paper's next intentional
semantic refresh. New-paper intake writes them prospectively at the freeze.

Workflow code, skill prose, logs, and advisory state are not paper semantic
inputs. A semantic audit correction must instead bump a structured version or
compatibility field retained by the canonical
`formalization_review_protocol_sha256`. Pure refactors and performance changes
outside a lane's pinned producer surface may discard only ignored scheduling
cache and must not reopen completed papers.
The append-only formalization-engine revision ledger classifies production-code
changes as review-compatible or review-semantic in CI; it is operational only
and never enters paper evidence, closeout plans, or material artifact identity.
`review_compatible` requires identical obligation and accept/reject meaning; it
does not waive a lane-specific semantic version. Raw receipts retain exact
producer-code provenance, but a producer-only mismatch may reuse only through
an append-only `raw_producer_compatibility` grant on a compatible ledger
revision. That grant must name exact predecessor and current producer identity
sets, run against clean registered HEAD, and require equality of the complete
schema-10 fingerprint after removing only the two producer-provenance fields.
Feature-scoped engine identities, source/map bytes, Lean closure, toolchain,
status, and all other inputs therefore still force reissue. Never infer this
compatibility from a paper, map key, declaration, function name, or a general
claim that a refactor is harmless; never cross a review-semantic transition.
Generate and validate the append-only update from the exact staged index; never
edit an earlier ledger entry.
Commit the registered transition before closeout. The planner and launcher
must require production engine sources and the ledger to match clean `HEAD`,
then validate that exact committed engine against the ledger; ignored and
untracked production sources and index flags that hide changes fail closed.
Structured-projection-neutral
protocol prose may remain dirty. Recheck after execution before accepting
success. This runtime gate is operational and does not by itself enter or stale
paper receipts or plan identity across `review_compatible` commits. It never
supersedes exact lane-specific producer or Lean-control pins, which continue to
invalidate their own selected receipt when changed.
Closeout snapshots retain exact raw-producer paths by evidence role while
excluding nonproducer engine implementation files. The only provenance reuse
exception is the registered semantic-fingerprint grant above; never classify a
map or claim by filename or function name alone.
Legacy Lean receipts keep their original bytes and hashes during control-list
migrations. Only the exact historical three-control tuple may use the retired
helper compatibility projection; every other missing/extra control fails.
Never rewrite or rerun an existing paper merely to adopt these workflow
mechanisms.

Execute only the planner's current `next_action`. If that action is
`strict_closeout`, run its exact argv, including `--deep-paper-prose`,
`--plan-identity`, or `--new-run` when present. Do not replace it with a bare
runner command. A current inspect action is a stopping action, not permission
to rerun. An exact current compiled cache skips a redundant standalone build;
the strict transaction still owns the required paper-root build receipt.
If the action is `freeze_then_raw_reissue`, run only its printed dedicated
wrapper; do not call the generic raw producer or bind a judgment sidecar in the
same transition. A current raw with a malformed judgment sidecar is a
reconstruction stop, not permission to reissue raw evidence.
The first such action in a batch binds an ignored repository-wide closeout
engine-wave snapshot. Keep the registered engine fixed through that wave. If a
later registered engine transition is necessary, the planner returns
`reset_closeout_wave_engine_snapshot`; run only its printed explicit reset,
then replan. Never reset a wave implicitly, and never edit the engine while a
raw action is active. The wrapper writes a bounded, non-authoritative terminal
receipt at
`papers/<PaperRoot>/.review_traces/source_record_raw_reissues/raw_reissue_operation.json`.
Use `--raw-reissue-status` to inspect a lost stream; it reports the record,
wave, and both locks, so do not infer completion from a lock disappearance. A
running or malformed record blocks a new raw action. Only after both locks are
idle may an operator run the explicit
`--acknowledge-stale-raw-reissue-operation`, which terminalizes operational
state only and requires a replan; it never starts a scan. The raw producer
requires that live wrapper lease and receipt-bound operation id, so a
hand-issued `--closeout-raw-reissue` cannot bypass predecessor preservation or
accidentally duplicate a scan. The wrapper rechecks the bounded paper/source
identity after it owns the lease and compares the exact captured wave after the
producer returns; either change stops for replan instead of retrying raw work.
If the action is `wait_for_source_record_scan`, do not invoke the wrapper or
poll it into a retry loop: wait for the lock holder, then run only its explicit
replan successor. Batch and commit raw-producer changes before a closeout wave;
never edit that producer while the repository source-record lock is held. Its
final mixed-input rejection protects evidence integrity, but is not a reason
to rerun unchanged work automatically.

Treat the strict closeout transaction as frozen and read-only. Any
planner-scheduled repair is a separate predecessor that ends in a replan:

- finish proof edits and any audit-engine bug fix before starting it;
- run a cache or sidecar refresh only when a named diagnostic or planner action
  directs it, never as a generic transaction prelude or from a strict closeout
  consumer;
- do not edit status, maps, reports, protocol, producer code, or imported Lean
  sources while it runs;
- let the repository command own the one final mutation check; nested lanes do
  not independently finalize or republish the same evidence; and
- after a failure, run only the named diagnostic lane or invalid item. Do not
  repeat an unchanged successful lane.

The closeout launcher runs the unchanged strict repository command in a
detached worker, acquires a per-paper duplicate-run lease, and atomically writes
non-authoritative execution state to
`papers/<PaperRoot>/.review_traces/paper_closeout_worker.json`. Its complete
output is in an immutable launch-specific ignored worker log. Use
`python3 scripts/run_paper_closeout.py --paper <PaperRoot> --status` to inspect
it. If a tool or terminal stream
disappears, inspect that state and log instead of starting another worker. A
matching completed current-input identity is idempotent; recovery or changed
inputs require the planner's explicit `--new-run`. Legacy completion is
inspected without forcing a rerun. A known successful legacy completion gets a
one-time ignored material baseline so a later real input change is detectable;
unknown or incomplete state is never adopted. State records what happened but
is never deserialized as semantic authority and changes no paper audit identity.
Non-authoritative does not mean disposable: do not manually delete, edit, or
copy worker state, log pointers, plan receipts, guard caches, or profile-specific
legacy adoption files. Use the planner and `--status`; deleting them can lose
recovery and recreate work.

The targeted strict transaction performs status-routed DAG, final-report, and
independent source-audit artifact checks plus prospective-intake preflight
before it constructs the expensive semantic context. Blocking artifact or
intake errors stop there; warnings carry into the later full status and semantic
findings. The planner's cheap placeholder scan covers only the explicit paper
root, `PaperInterface.lean`, and paper-local `Assumptions.lean` when present;
the strict transaction owns authoritative transitive Lean-graph validation.

Paper-local status rendering is also scoped:

```bash
python3 scripts/sync_paper_status.py --paper <PaperRoot>
python3 scripts/sync_paper_status.py --paper <PaperRoot> --check
```

These commands touch/check only paper-owned README/legacy-note outputs. The
strict closeout already reads paper-local `status.json` and does not require
aggregate status, documentation, or site reconciliation. Run the unscoped
status sync once at integration, public-PR, or release time.

Classify a proposed audit write before creating any plan, archive, or sidecar:

- A human statement receipt changes only when its exact source target, Lean
  signature/translation, source-route evidence, or reviewer ledger changes.
  An all-reuse plan with zero fresh targets and zero retirements is a no-op;
  do not write a new sidecar or archive. The reissue tool refuses that rewrite
  by default. Its `--allow-all-reuse-rewrite` escape hatch is only for an
  explicitly approved storage migration and is not a semantic audit action.
- A raw source-record scan is machine-generated aggregate evidence, not a
  human judgment. Report it as a raw refresh, never as a receipt reissue.
  Reuse the existing per-item judgments only through their exact semantic
  identities or an authenticated semantic rebind.
- Lean-derived closure fingerprints inside a validated source-to-Spec
  correspondence belong to the strict correspondence lane. Refreshing those
  five machine receipts cannot by itself reopen a source claim, source atom,
  binding, disposition, or human review. Any other or malformed correspondence
  change fails closed and requires ordinary review.
- `FINAL_CLOSURE_RECEIPT.md` is a closure binding, not a new semantic review.
  Update it once after its selected evidence lane and focused build pass on one
  frozen input set. Never create a second “final validation,” “closeout,” or
  “current receipt” document to narrate the same paper state.

### Audit Artifact Retention

Keep configured, tracked audit sidecars at their canonical paths even when a
report classifies them as historical evidence; do not hide canonical paths with
a broad `audit/*.json` ignore rule. Put retry outputs, templates, recovery
fragments, and other non-authoritative scratch material under ignored
`.review_traces` or `.scratch` instead, never in a current evidence path.

At an explicit cleanup boundary, make a checksum/path manifest before removing
untracked scratch artifacts. A partially generated canonical raw reissue may be
restored to its committed snapshot only after the current status, report, and
claim map are verified not to depend on its worktree bytes. Preserve current
source maps, reports, statuses, direct review ledgers, and tracked human
validation logs. Purge regenerable trace caches only after active writers have
exited; retain a tracked validation log and any live operational plan/lock until
the owning workflow has reached its next explicit boundary.

It runs focused evidence integrity and conclusion provenance in-process after
the primary paper gate passes, sharing exact current identities and stopping
before a later expensive lane when an earlier lane fails. Standalone component
commands are diagnostic, not mandatory reruns after an unchanged pass. Strict
dashboard closeout uses one fresh batched Lean manifest attestation while
retaining item-level reuse of unchanged semantic judgments; editable dashboard
cache rows are not acceptance evidence. A persistent Lean manifest may be read
only when its declaration authority is independently reconstructed from current
exact source and validated evidence. If that is unavailable, do not inspect or
publish the store; use the one fresh batch already required by closeout. Do not
resume an interrupted refresh from a journal alone. A journal is scheduling
data only: resume entries may seed the in-process cache only when their exact
current context and source coordinate match, their Lean payload exactly matches
an independently authenticated carrier, and current Lean-owned dependencies
are reattached. Any missing carrier, changed context, ambiguity, or malformed
entry is a fresh-manifest miss, never a reason to reuse or publish authority.
Do not let a stale Lean-to-TeX presentation receipt hide an otherwise current
statement judgment: report projections may use a unique direct statement
receipt only when exact signature, Lean text, source text, and translation
digests all agree; duplicate presentation receipts still fail closed.
Do not
use a repository-wide
build as the default paper closeout. Use `lake build` without a paper target
only for integration or release milestones. Do not run concurrent Lake builds
in one worktree. Likewise, run focused Python test modules for a changed audit
lane during development; the complete `scripts/tests` suite is an audit-engine
integration or release check, not an ordinary paper-closeout requirement.

Use `--closeout-trace` only to diagnose time or reuse counters. The trace is not
acceptance evidence. Cache, archive, `.review_traces`, and scratch output must
never enter a semantic invalidation set merely because of its location. Lean's
loaded module graph defines canonical source membership, and the same frozen
closure/source snapshot must be shared by declaration indexing, manifest
extraction, source-record validation, and final mutation checking.

For a manifest job that can outlive one tool-output yield, use a non-PTY,
non-login process and make the process itself write its result and diagnostic
log atomically to an ignored persistent path. The chat/tool stream is progress
only, not the result transport. If the stream or session handle disappears,
check the process and the content-addressed artifact before retrying; never
launch a duplicate elaboration merely to recover stdout.

Before final status or release readiness, read
`references/post-formalization-closeout.md` and
`references/final-closure-receipt.md`. `formalized` means the entire selected
normal source surface has correct paper-facing statements, closed Lean proofs,
current semantic evidence, and no hidden unresolved obligation. Human or
independent release certification is a separate claim.

## Detailed References

Load only the reference needed for the active task:

- `references/formalization-handbook.md`: searchable detailed legacy handbook;
  current policy overrides conflicts.
- `references/post-formalization-closeout.md`: report, DAG, audit, and closeout.
- `references/final-closure-receipt.md`: canonical closure artifact and
  invalidation rules.
- `references/public-private-sync.md`: private/public export and history safety.
- `references/proof-strategies.md`: general proof patterns.
- `references/proof-foundations-math.md`: foundational mathematics.
- `references/proof-foundations-probability.md`: probability and measure theory.
- `references/proof-foundations-optimization.md`: optimization and convexity.
- `references/proof-algorithms-complexity.md`: algorithms and complexity.
- `references/proof-algorithms-online.md`: online algorithms.
- `references/proof-markets-social-choice.md`: matching, voting, and markets.
- `references/proof-mechanism-design.md`: auctions and mechanism design.
- `references/proof-recommender-systems.md`: recommender-system models.

For Lean style in newly written or substantially changed code, use
`skills/lean-community-conventions/SKILL.md`. For external AI-formalization
workflow patterns, consult `skills/ai-formalization-workflows/SKILL.md` without
letting it override the repository protocol.
