# Agent Formalization Workflow

This file is for agents and maintainers. The top-level `README.md` is protected
hand-written human-facing project prose. Do not edit it unless the user gives
specific root-README instructions.

`config/formalization_audit_protocol.json` is the normative machine-readable
protocol for audit versions, source scope, reuse identity, builds,
assumption/correction categories, and proof-campaign pacing. This document
explains that protocol but does not override it. Historical paper reports may
accurately name older artifact schemas without changing the current protocol.
Validate the policy before changing workflow behavior:

```bash
python3 scripts/formalization_protocol.py
```

## Documentation Split

- Human-facing docs should be strategic, short, and readable without Lean
  expertise. The top-level `README.md`, paper-root
  `FINAL_VALIDATION_REPORT.md` files, `PaperInterface.lean`, and
  `docs/DependencyDAG.pdf` are the main human surfaces. Use
  `VALIDATION_MODEL.md` to explain status labels.
- Agent-facing docs may be detailed and operational. This file,
  `docs/ARCHITECTURE.md`, `docs/ECONCSLIB_DOMAIN_INDEX.md`, and
  `skills/econcs-formalizer/` contain workflow rules and implementation
  conventions. Use `skills/econcs-prover/` for active Lean theorem proving and
  proof repair.

Do not put long theorem ledgers, raw command transcripts, or proof-internal
details in the top-level README. Do not add generated blocks or generator
outputs there. If the user explicitly asks for a root README edit, make only
that edit. `python3 scripts/root_readme_policy.py` enforces the non-generated
README policy; content hash locks are intentionally not used.

## Starting A Paper

Ask the agent to use the `econcs-formalizer` skill for paper workflow and the
`econcs-prover` skill once theorem proof work starts. Give it the source PDF or
paper URL. A good first prompt is:

```text
Get context on this repo using the skill file. Then start formalizing
<paper title>. Build a source inventory first: every paper definition, named
lemma/proposition/theorem/corollary, source-labelled theorem-like claim, and
explicitly named source assumption/model condition.
Use `named_theoretical_statements` unless the user explicitly requests the
deep all-prose mode. Build a compact proof plan that records the next proof
seam, source assumptions, and dependencies before proving in Lean.
```

## Source Scope And Reuse Baseline

This baseline supersedes older workflow passages that ask for routine
cataloguing of all prose or whole-paper cache invalidation.

- A closeout map must explicitly declare `source_coverage_mode`. In normal
  `named_theoretical_statements` mode, the required surface is source-presented
  named theoretical statements: definitions, results, theorem-like claims,
  explicitly named assumptions/model conditions, and named appendix results.
  Standalone formulas, equations, algorithms, figures, captions, tables,
  numerical examples, simulations, empirical observations, and narrative prose
  are deep-audit material. A standalone display may still be inspected as a
  dependency of a selected named item, but it receives no independent normal
  coverage row.
- Complete normal-scope coverage with a source-only named-presentation index
  from a pinned UTF-8 text/TeX audit artifact. The receipt must record current
  artifact bytes, index digest, and any declarative source environment/heading
  mappings. A source map cannot certify its own completeness. An unknown
  named presentation blocks closeout until it is classified; a named open
  question is recorded with an explicit source-declared-open nonproof
  disposition, not silently ignored.
- Map keys, aliases, Lean declaration/function names, and raw pretty-printed
  declaration spelling are navigation only.
  Direct coverage requires a pinned source semantic item, a byte-validated
  source anchor, and one unique current fully elaborated Lean signature with
  the checked semantic contract. A rename or equivalent surface rewrite can
  rebind only through those unique semantic identities; refresh the raw text
  as trace evidence after matching, and fail closed on ambiguity.
- Cache reuse is per item. It requires the current audit schema, unchanged
  source semantic digest, byte validation of the current source quote on every
  normal source check, and a unique current Lean signature plus transitive
  elaborated proposition/type dependency context. Exact module artifacts are
  pinned only for opaque imported terminals whose bodies are unavailable to
  that graph; whole review-module artifacts, unrelated declarations, and
  theorem proof bodies do not invalidate an unchanged statement judgment.
  Its identity also pins the configured item and resolved qualified Lean route,
  plus the configuration/preflight and validator fingerprints. Re-run static
  configured-route validation before accepting a cached result; an unresolved,
  stale, or ambiguous route fails closed. Unrelated source edits and
  navigation-only moves do not reopen an unchanged item.
  Ordinary reads do not write sidecars; explicit refresh commands are the only
  cache writers.
- A legacy `paper-coverage-v4-semantic-proof-and-pinned-defect-support`
  sidecar is not current evidence and is never silently upgraded. Use
  `python3 scripts/semantic_audit_reuse.py --paper <paper> --migrate-legacy-v4-coverage
  --previous-source-map <pre-change-map> --previous-review-cache <pre-change-cache>`
  only when both historical snapshots are available. The migration is explicit
  and atomic: every legacy item must identify one prior source target by exact
  digest, retain the same full source semantic/anchor pin in the current map,
  and rebind each old review row to one current row with unchanged
  declaration-name-independent elaborated manifest structure, verified
  old/current signatures, and unchanged reviewed statement text. Source keys,
  row names, and Lean declaration names navigate snapshots only. Any missing,
  stale, changed, or ambiguous identity leaves the v4 file untouched for a
  fresh semantic audit.
- Proof work comes first after target setup. Update plans, reports, or DAGs at
  material source-scope/assumption repairs, handoff, paper transition, or
  closeout, rather than on a timer or after every helper lemma.
- When normal-scope review uncovers a real unnumbered prose defect, retain it
  in `audit/source_proof_fidelity.json` as a `deep_audit_observations` record
  instead of deleting or misclassifying it as a named theorem. Pin its source
  locator and affected locators to the ledger's canonical source artifact,
  state the claim, finding, and repair handoff, and link it only to
  byte-pinned `source_kind` deep-only map rows that the semantic source
  selector excludes from normal scope. This is unavailable in deep all-prose
  mode and can never carry a defect resolution, corrected target, or scope
  waiver. It records future work; it does not change named-theory status.

### Theorem-Realization V11

New papers and explicitly requested v11 upgrades set
`review_surface.require_source_spec_correspondence: true`. It becomes a
closeout gate for `formalized` and `formalized with caveat`, not an immediate
error for a `not started` statement skeleton. Before Lean drafting, independently
inventory every material source atom from exact pinned source-quote bytes. This
is source-side semantic work: theorem, binder, field, function, map-key, and
type names are navigation only.

A material repair of a trusted legacy-v10 paper instead needs a current
item-level v10 source and Lean review. It does not silently manufacture a v11
source-to-Spec migration. An explicit v11 marker always strengthens this rule.

For each claim-bearing endpoint at closeout,
`source_spec_correspondence_schema: 1` requires a transparent `Spec : Prop`, a
theorem/lemma whose Lean Meta type is exactly that `Spec`, plus
atom-to-elaborated-Spec coverage and a full Lean closure receipt. The closure
includes implicit proof and typeclass/instance arguments.
Every material terminal has one explicit disposition: source atom, approved
source correction/additional assumption, checked Lean derivation, or
version-pinned foundation basis. No declaration, data, record, container,
carrier, or function shape receives automatic credit. A written semantic bridge
is independent review evidence, not a self-certifying assertion.

Reuse this lane per item only when the source atoms and exact quote pins, Spec
closure, narrow closure environment, and theorem type are unchanged. Legacy v10
records remain readable but cannot silently become v11 credentials.

The agent should think through the proof and formalization plan outside Lean
before proving, especially where the paper is underspecified. Keep that plan in
the private workspace as `FORMALIZATION_PLAN.md` and update it as the proof
route changes. Do not publish planning, handoff, or progress markdown in the
public paper folder unless the user explicitly asks for that artifact.
At the beginning of every paper audit or new formalization, the first plan
section should be an extended outside-Lean paper sanity pass: read the source,
check every named result and formula-bearing displayed claim for plausible
signs, constants, normalizations, quantifiers, domains, and dependencies. Also
ask which generalizations, conjectures, or extensions look trivial or
near-trivial once the source theorem chain is formalized. Write the initial
findings in `FORMALIZATION_PLAN.md`. Use those findings to choose the
formalization strategy. If the pass finds a likely source bug, missing
assumption, formula ambiguity, or issue that could change the theorem target,
tell the user early before encoding the printed formula as a proof premise.
Do not turn a routine equality/inequality ambiguity, including `=` versus
`<=`/`>=` or strict versus weak endpoints, into a long proof campaign by
default. Ask the user when available. Otherwise record the exact condition as a
visible additional assumption in the corrected theorem and post-formalization
report, continue with actionable work, and raise it at the next interaction;
do not silently credit the condition to the source.

That initial pass is a narrow start gate. Before deep Lean proof work, the plan
must record the sections from
`skills/econcs-formalizer/templates/FORMALIZATION_PLAN.md`, including:

- the source/version inventory, including official source, open source, local
  cache paths, and version mismatches;
- the source-only named-presentation receipt and the normal named-theory
  ledger, including every source-presented named definition, proposition,
  lemma, theorem, corollary, theorem-like claim, and explicitly named
  assumption/model condition; track standalone displays or algorithms only in
  deep mode or as dependencies of one of those selected items;
- the formula/dependency sanity pass, including density-vs-mass representation
  issues and which prior paper objects each result depends on;
- the source assumptions/dependencies and next proof seam; do not make a broad
  generalization/conjecture/extension scan a gate to beginning proof work;
- the shared-library reuse checkpoint for mathlib, cslib, optlib, potential
  upstream Lean sources from
  [`UPSTREAM_LEAN_SOURCES.md`](UPSTREAM_LEAN_SOURCES.md), and existing
  `EconCSLib` APIs, including citation/provenance for any upstream material
  used or ported;
- the formal target map, including rows to fully prove, empirical/out-of-scope
  rows, and any explicit boundary that would remain if the paper cannot be
  closed immediately;
- the next proof target and its focused build command.

## Required Paper Artifacts

Each public paper folder should keep the root focused on executable paper code
and machine-readable status. It should contain:

- `.gitignore`
- `MainTheorems.lean`
- `PaperInterface.lean`
- `status.json`
- `review-dashboard.sh`
- `FINAL_VALIDATION_REPORT.md` when a paper has a final validation claim
- `FINAL_CLOSURE_RECEIPT.md` for a closed paper
- `docs/DependencyDAG.tex`
- `docs/DependencyDAG.pdf`
- `audit/*.json` for tracked source maps, statement reviews, and closure evidence
- locally cached source PDF, ignored by Git
- locally cached `pdftotext` extraction, when licensing permits

Private paper folders may additionally keep `README.md`,
`FORMALIZATION_PLAN.md`, handoff notes, source audits, and other progress
documents. Keep those private by default.

Completed papers should also have:

- `ProofInterface.lean` when implementation-facing theorem endpoints would make
  `PaperInterface.lean` too large to review directly.
- `ProofLedger.lean` when an exhaustive source-numbered proof endpoint ledger is
  useful. Do not create new `PostPaperAudit.lean` or `AuditLedger.lean` files;
  they are not human-facing audit surfaces and should be consolidated into
  `ProofLedger.lean` during ordinary maintenance.
- `FINAL_VALIDATION_REPORT.md`, ending at Section 11, with the paper-facing
  disposition, definitions, named theorem statements, genuine deviations,
  assumptions, gaps, and caveats.
- A concise caveat-repair memo when the final status is `formalized with
  caveat` because of a substantial error in a central paper claim and a fully
  proved corrected endpoint. Prefer a TeX source plus rendered PDF with a 1--2
  page executive summary and deeper notes for each issue. The details should be
  human-facing proof text, not a Lean declaration inventory: quote or restate
  the old source equation/statement, give the exact replacement
  equation/statement, explain why the change is substantive, and include a
  short TeX derivation when the caveat is algebraic.
- A concise `docs/SOURCE_CLARIFICATIONS.md` only when a current mathematical
  source reading needs explanation. State the source anchor, current reading,
  and result-level effect; do not record audit chronology, proof-repair history,
  or Lean implementation detail there.

## What The Agent Should Keep Current

- `status.json`: paper-local source of truth for paper status, dashboard review
  rows/slices, interface metadata, and artifact paths. At a paper-local status
  freeze, run `python3 scripts/sync_paper_status.py --paper <paper>` and its
  `--check` form to render/check only that paper's owned README or legacy-note
  projection. Do not hand-edit those generated paper-local files or rows. The
  root `README.md` is not a generated status surface; the sync script enforces
  its protected lock. Do not run the aggregate generator after every status
  edit or as a paper-closeout prerequisite. Aggregate `papers/status.json`,
  `papers/human_status.json`, `docs/PAPER_STATUS.md`, and `site/index.html`
  projections belong to a separate integration, public-PR, or release boundary.
  The sync script defaults to tracked paper status files so local draft
  scaffolds do not pollute CI-facing generated tables; pass
  `--include-untracked` only when intentionally syncing a new untracked paper
  scaffold. In a dirty shared checkout, run an aggregate sync only from a clean
  integration worktree so it cannot publish another lane's intermediate status.
  A paper closeout receipt binds the paper-local status input; aggregate
  projections are not a second evidence gate.
- `status.json` `human_summary`: public-facing prose for the generated tables.
  If `human_summary_review.status` is `human_written` or `human_approved`, do
  not rewrite the summary unless a human explicitly asks for that exact edit.
  Audit scripts may require a nonempty summary for non-formalized papers, but
  should not pressure edit or shorten human-written or human-approved prose.
- Private `FORMALIZATION_PLAN.md`: lightweight outside-Lean proof scratchpad.
- `docs/DependencyDAG.tex`: proof map with every named result and definition-like
  paper object represented; status and caveat text should agree with
  `status.json`.
- `MainTheorems.lean`: implementation-level source-faithful wrappers.
- `PaperInterface.lean`: the single canonical human-review Lean surface and
  the only allowed `review_surface.source_file`, with readable paper
  definitions and named theorem statements.
- `AuditInterface.lean`: optional implementation/proof-support surface for
  bulky aliases and helper endpoints. It may be imported by
  `PaperInterface.lean`, but it must not be configured as the review surface.
- `ProofInterface.lean`: optional implementation-facing theorem endpoint
  surface for broad wrapper families and proof-seam checks.
- `ProofLedger.lean`: optional exhaustive proof endpoint ledger when useful;
  `PostPaperAudit.lean`/`AuditLedger.lean` files are not review surfaces and
  should be consolidated into `ProofLedger.lean` during ordinary maintenance.
- `FINAL_VALIDATION_REPORT.md`: final human report.
- `audit/*.json`: LLM-as-judge, source-statement-map, source-record, and
  assumption-provenance sidecars.

Completed papers with a configured source-proof fidelity ledger must use
schema 2. Every defect entry needs `status_impact` and
`status_impact_rationale` under the rule in
[`FORMALIZATION_STATUS_POLICY.md`](FORMALIZATION_STATUS_POLICY.md). Treat
`statement_impact` and `status_impact` as different questions: the former says
whether source proof text or a source statement changes; the latter says
whether the issue is a note, a substantial paper caveat, or evidence that the
formalization remains partial.

For the 2026-07-18 migration of completed papers explicitly marked
`repository_visibility: public`, use the frozen inventory, sequential commands,
and live receipts in
[`PUBLIC_COMPLETE_PROTOCOL_AUDIT_2026-07-18.md`](PUBLIC_COMPLETE_PROTOCOL_AUDIT_2026-07-18.md).
The batch `--public-complete` diagnostics select this visibility/status set;
they do not establish that a prepared public candidate is release-safe and do
not replace a paper-local source-first closeout.

Do not waive a named mathematical proposition as empirical description merely
because it applies a generic theorem to a dataset or concrete mechanism. Raw
measurements and figures may be non-theorem scope; the proposition's model
instantiation, exact/tight conclusion, and any algorithmic guarantee must be
proved or recorded as a partial boundary.

If the paper proof is imprecise, the agent should build a defensible proof
strategy, formalize that strategy, and record the deviation in the validation
report. It is better to prove a source-faithful theorem by a cleaner route than
to spend large amounts of time following an informal proof line-by-line, as long
as the theorem statement and assumptions are explicit.

## Post-Formalization Closeout

Before declaring a paper complete, run a library elevation pass over the
paper-local proof modules. Check whether any proof results, proof techniques,
certificate constructors, model-neutral definitions, or reusable primitives
should move into `EconCSLib` for other papers to reuse. Elevate local/low-risk
items when the destination module is clear and the build can be checked. If the
move needs broader API design, keep the paper-facing wrapper in place and record
the candidate, destination module, and reusable proof idea in
`FINAL_VALIDATION_REPORT.md`.

Library certificate APIs are allowed and often preferable. A reusable theorem may
require an explicit certificate, witness, external-boundary hypothesis, or
source-row package from its caller. That makes the library theorem a conditional
tool, not a paper result by itself. A paper-facing theorem that calls such a
library API is fully formalized only if it constructs the certificate from the
paper source primitives inside Lean, or if the certificate is a validated
paper-source assumption. Otherwise the paper endpoint remains partial or
conditional. During closeout, run the combined axiom/premise/source-hygiene
audit when you need a repository-wide provenance snapshot, and write its
paper-by-paper report:

```bash
python3 scripts/audit_repository.py --include-active --library-premise-audit --info-limit 0 --write-report docs/RECURSIVE_PROVENANCE_AUDIT_<date>.md
```

Use `--include-active` when the paper under review is still listed as active;
otherwise it is fine to omit it. The generated report is the durable closeout
artifact for Lean axiom closure, broad/opaque paper-facing rows, direct visible
premises, source-row formula boundaries, and source-shaped reusable APIs. A
completed paper must have no theorem-status findings for its folder unless the
exact boundary is marked partial/conditional in `status.json`, the dependency
DAG, and the final validation report.
An added non-source assumption, narrower Lean model, or weaker semantic endpoint
is such a partial boundary even if the restricted theorem is internally proved.
Do not promote that case to `formalized with caveat`; reserve the caveat status
for a substantial source-paper error whose corrected endpoint is fully proved.
This audit checks tracked LLM sidecar freshness; it should not rerun LLM judges
for every paper. Refresh judge sidecars only for the target paper rows/records
that are stale, missing, or explicitly requested. An all-paper judge refresh is
a separate user request, not part of ordinary post-formalization closeout.

Also run
`python3 scripts/audit_repository.py --library-only --library-premise-audit --info-limit 0`
after reusable-library edits to fail source-shaped reusable APIs, hidden
proof-boundary section variables, axiom/opaque placeholders, and guarded debug
commands, and to list shared-library APIs with certificate/source-boundary
parameters. Then check that no completed paper wrapper still exposes one.
The same pass rejects reusable `Assumption`/`Hypothesis` declarations and
paper/source provenance wording in `EconCSLib/*.lean`, and requires the
root-imported `EconCSLib.LibraryDefinitionAudit` module for standard-name
definitions. When adding a standard wrapper such as a convexity, concavity,
order, metric, or probability notion, add a build-checked equivalence lemma in
that audit module against the mathlib or local canonical definition.
Use `--info-limit -1` when you need the complete direct library-boundary
inventory; CI uses `--info-limit 0` so only actionable errors/warnings appear.
The ordinary audit runs Lean-native `#print axioms` on paper-facing interface
rows to catch transitive global proof debt exactly. It separately checks
expanded `#check` statements and direct paper-local alias targets for visible
certificate/source-boundary premises. Ordinary inequalities, positivity, and
measurability side conditions are different: if they are visible in the
paper-facing statement, the statement/assumption judges validate them against
the source, and a caller may derive them from stronger visible source premises.
Do not use `axiom`, `constant`, `opaque`, or unsafe declarations to stand in
for missing source proofs.

Do not hide paper-source formulas inside reusable-library definitions. If a
formula is paper-source data used by a selected named result, expose it in that
result's transparent realization path or as an explicit certificate argument
to the reusable theorem. It needs its own `PaperInterface.lean` review row only
when it is independently presented as a named theoretical source statement;
standalone displays remain deep-only inventory items. If the formula is generic
and derived from library primitives, keep it generic and avoid
paper/result-specific names. The library premise audit rebuilds a fresh in-memory declaration index
on every run and reports direct certificate/source-boundary APIs and
source-shaped reusable definitions; do not check in a dependency index.
The reusable-library parser covers theorem, lemma, def, abbrev, structure,
class, and inductive declarations. A proof-boundary structure or package may
live in `EconCSLib/`, but a paper-specific formula/window/row/source name should
not be baked into the reusable API.

The repository audit also includes a source-hygiene pass for generic code. It
discovers paper IDs and citation prefixes from the `papers/` folders, then
rejects those concrete references in reusable code, audit scripts, and generic
workflow docs. It also rejects paper theorem-number labels such as `Theorem 2`
or `Lemma 4.1` in `EconCSLib/` comments. The check is intentionally standard-
based rather than function-name-based: paper metadata belongs in paper-local
files or data config, source theorem numbering belongs in paper interfaces and
validation reports, and reusable code should use domain or algorithm names.
If a term is genuinely an established algorithm/domain name, allow it in
`papers/audit_config.json`; do not add code-level one-off exceptions.

This hardened audit catches the recurring mechanical failure modes: hidden
source-row/certificate premises in paper wrappers, transitive proof debt via
Lean-native `#print axioms`, source-shaped reusable APIs, and hardcoded
paper references in generic code. It does not prove that every source formula is
mathematically correct by itself. That requires the outside-Lean formula sanity
pass, derivation of formula-bearing claims from primitives where possible, and
the statement/assumption judges for visible paper-facing text.

## Human Review Order

When the agent says a paper is done, inspect:

1. `FINAL_VALIDATION_REPORT.md`
2. `PaperInterface.lean`
3. `docs/DependencyDAG.pdf`
4. `status.json`
5. `ProofLedger.lean`, only if an exhaustive proof endpoint ledger is needed

The post-formalization audit must inspect the report and DAG before handoff.
After the final report, post-formalization audit, or DAG source changes, freeze
those inputs and begin the closeout with:

```bash
python3 scripts/closeout_reuse_plan.py --paper <paper>
```

Execute only its current `next_action`; when it schedules strict closeout, use
the exact `run_paper_closeout.py` command it prints. That worker owns the
targeted DAG/final-report and semantic closeout gate: completed or conditional
papers must name the DAG TeX/PDF artifacts, record rendered/visual DAG
inspection evidence, include validation checks, and avoid stale placeholder
language such as `not checked` or `not run`.

When the planner schedules a raw reissue, do not interleave a build, dashboard
refresh, or sidecar write. Freeze inputs, issue one raw candidate, validate any
authenticated structural replay against that exact raw/map pair, then compute
reuse and materialize only the remaining semantic delta. A changed input returns
to the planner; an unchanged failure is inspected rather than retried. Check a
busy source-record worker with
`python3 skills/econcs-formalizer/scripts/source_record_audit.py --root . --lock-status`.
That command is diagnostic only: never delete or replace the lock to force a
new scan. Execute a planned raw reissue only through the printed
`closeout_reuse_plan.py --execute-freeze-raw-reissue` wrapper. A current raw
with a malformed judgment sidecar needs reconstruction, not a raw scan.

For a named failure diagnosis only, a maintainer may run the underlying audit
without creating a competing execution record:

```bash
python3 scripts/audit_repository.py --paper <paper> --paper-closeout --include-active --info-limit 0 --no-closeout-state
```

That direct diagnostic cannot establish closeout acceptance. Re-enter through
the planner after the diagnosis or any repair; do not treat a passing direct
child invocation as a replacement for a planner-issued receipt.

Agent/formalization readiness is separate from saved human dashboard review.
If Lean builds, statement/assumption validators are current, the
paper-closeout audit passes, DAG/report evidence is current, and generated
status files are synced, the paper may be reported as formalized even with
`0/N` saved human review entries. The final report must still disclose the
human review count; if a release requires human approval, track that as a
separate promotion gate rather than as Lean proof debt.

The human-facing files should let a reader compare the formalized statements to
the paper without opening lower proof files.

Do not add filename variants for the review surface. If `PaperInterface.lean`
has hundreds of declarations, it is too broad; move helper/proof endpoints into
`ProofInterface.lean` or `ProofLedger.lean` and keep the dashboard-facing
file small.
The dashboard surface should usually be close to the paper's named definitions
and named results. Slices help reviewers navigate a real source-facing surface;
they are not a substitute for removing helper endpoints from `PaperInterface.lean`.

## Validation Commands

For reusable library work during active paper development, stay targeted:

```bash
lake build <touched-library-module>
lake build <active-paper-root>
git diff --check
```

Do not run a broad/full repository build merely because a shared library file
changed while the paper is still in progress. Save broad builds for natural
stopping points: the paper is complete or being handed off, you are about to
commit/push a significant integration batch, preparing a public PR/release, or
the user explicitly asks for a broad integration check.

At integration, release, or an explicitly requested repository-wide stopping
point, broaden validation as appropriate:

```bash
lake build EconCSLib
python3 scripts/sync_paper_status.py --check
python3 scripts/audit_repository.py --include-active --library-premise-audit --info-limit 0
git diff --check
```

The broad audit checks whether existing LLM-as-judge sidecars are current. It
does not require regenerating or rerunning judge sidecars for every paper unless
the user explicitly asks for an all-paper refresh.

For paper closeout or post-formalization work, batch the final report and DAG
updates, freeze them, and run the planner:

```bash
python3 scripts/closeout_reuse_plan.py --paper <paper>
```

Follow only its dependency-ordered action. Treat the paper-specific DAG/report
findings from its strict worker as blockers for a completion claim, even if
unrelated global repository findings remain. Use a direct
`audit_repository.py --paper-closeout --no-closeout-state` invocation only to
diagnose a named failure; it is not a closeout result.

The unfiltered full repository audit is a closeout/public-promotion check. It
is available through manual CI dispatch and should not run on routine push/PR
CI for ordinary documentation or proof-development churn.

At paper closeout, build the complete paper root serially:

```bash
env LEAN_NUM_THREADS=1 lake build <PaperRoot>
```

Use `lake build <PaperRoot>.PaperInterface` only as a faster proof-iteration
check. Passing the interface alone is not a paper closeout build.

The full target:

```bash
lake build EconCSLib
```

is an integration/public-release gate when that aggregate target is part of the
prepared release. It is not the default per-paper closeout command. During
private paper development and closeout, use the focused interface and complete
paper targets above; do not present a branch as public-ready until the release
integration target is green.

For statement-facing checks, prefer the paper-local launcher from the paper folder:

```bash
./review-dashboard.sh
```

On WSL2, the launcher binds broadly by default and prints multiple Windows
browser URLs when it can detect both localhost and the WSL guest IP. If the
browser does not pop or one URL fails, keep the terminal running and try the
other printed URL. Large interfaces may need several seconds before the first
page responds.

On startup it prints stale-check diagnostics against any existing logged reviews, so
you can refresh only the changed theorem checks and avoid re-validating unchanged items.
The dashboard also shows compact paper-source action links (open PDF/text file) for
quick jumps back to the source statement when needed.
Paper-side formulas are rendered with MathJax when they look like LaTeX.

At the beginning of a paper, run a lightweight statement target-setting pass
before spending much time on proofs:

1. First complete the `FORMALIZATION_PLAN.md` initial outside-Lean paper audit:
   source/version inventory, source-only named-presentation receipt,
   formula/dependency sanity check, shared-library reuse checkpoint, formal
   target/boundary map, suspected bugs or source ambiguities, and the next
   proof seam. Pin the exact artifact bytes used by that inventory with
   top-level `source_artifact_path` and `source_artifact_sha256`; an URL or
   digest without the bytes is not source evidence. Use normal
   `named_theoretical_statements` scope unless the user asks for the explicit
   deep all-prose audit.
2. Independently inventory every material source atom from exact pinned quote
   bytes, then build the initial source inventory and a compact
   `PaperInterface.lean` skeleton containing every in-scope paper-facing
   definition and named statement. In normal mode, do not create independent
   rows for ordinary prose, captions, figures, tables, numerical examples,
   simulations, or empirical material. Record an unlabelled condition only
   when it is a dependency of an in-scope item. Give each in-scope
   theorem/formula claim a transparent complete source-shaped `Spec : Prop` and
   a theorem/lemma with exactly that type, using `by sorry` only as the temporary
   private proof body. Do not use `axiom`, `opaque`, a theorem package, or a new
   assumption to make the skeleton compile. Identifiers and type/container shape
   cannot fill an atom or source-semantic gap.
3. Generate `audit/lean_to_tex_llm.json` from those Lean statements alone, with no
   paper context. The translation must preserve every visible binder,
   hypothesis, domain condition, equivalence/implication direction, and
   conclusion.
4. Generate `audit/statement_match_llm.json` by asking a separate judge to compare
   only the complete original paper statement and the Lean-to-TeX draft. A
   `matches` verdict requires the same hypotheses, subparts, quantifiers,
   domains, constants, normalizations, signs, inequality directions, and
   conclusions; conditional wrappers, omitted source subclaims, source-row
   packages, and broad aggregates must be marked `mismatch` or `uncertain`.
   The source curator and this judge must independently check that the
   `source_obligations` list exhausts the complete pinned excerpt; its strings
   are curated semantic atoms, not mechanically guaranteed by the source
   statement digest.
5. Run `python3 scripts/audit_conclusion_provenance.py --paper <paper> --json`
   on the skeleton. Resolve conclusion-bearing inputs before proof work; a
   `sorry` is more honest at this phase than importing the target through a
   premise.
6. Run `python3 scripts/review_dashboard.py --paper <paper> --refresh-cache` to
   regenerate the Lean declaration manifests, then run
   `python3 scripts/review_dashboard.py --paper <paper> --statement-precheck`.
   Finish the paper's focused Lean build before freezing the reviewed
   signatures. Reuse unchanged rows at item granularity: source semantic digest
   plus current quote anchor plus unique elaborated signature/dependency
   fingerprint. For v11 realization evidence, the item identity additionally
   binds source atoms, Spec closure, narrow closure environment, and exact
   theorem type. Do not invalidate an entire paper because another paper or an
   unrelated source line changed. Serialize explicit cache writers against the
   same paper surface, but normal JSON/precheck reads are read-only. Refresh
   only after the relevant interface/source-map/sidecar evidence changes, not
   after a report-only edit or every proof helper.
7. Run `python3 scripts/review_dashboard.py --paper <paper> --assumption-precheck`
   before treating statement matches as certified targets. The statement judge
   is row-local; it does not prove that theorem premises are source assumptions
   or derived facts.
8. Fix mismatches by editing `PaperInterface.lean` unless the translation is
   plainly wrong. Treat unresolved uncertainty as an explicit source/target
   ambiguity before proof work begins.
9. Record the current schema-6 canonical Lean declaration-manifest SHA-256 for every
   matched row in `FORMALIZATION_PLAN.md`. This is the statement freeze. V6
   includes definition/abbreviation values and name-free fingerprints of
   repository-local reducible dependencies, rather than freezing only a
   theorem's surface type. Implement proofs by
   replacing `sorry` without changing the elaborated type. If a type changes,
   its judgment is stale and steps 3--9 must be repeated for that row.

This initial pass is intentionally smaller than the full review workflow: do not
update the DAG, final validation report, human-review log, or review-surface
audit just for this target-setting pass. Its purpose is to make sure the Lean
statements are the right theorem targets before they become expensive to prove;
it is valid only together with the assumption/hidden-premise check above. Draft
`sorry` bodies are allowed only in this private target-setting phase; every
closeout/publication check must reject them.

Pinned source artifacts are ignored by default for redistribution safety. A
fresh checkout therefore cannot reproduce the source-byte attestation unless a
secured CI input downloads/provisions the exact artifact and verifies its hash,
or the artifact was deliberately tracked after a rights review. In the absence
of those bytes, CI must report source certification pending; never turn the
recorded digest alone into a pass.

At final closeout, the repository audit is the enforcement layer for the same
evidence. Completed papers should fail `python3 scripts/audit_repository.py` if
statement-translation sidecars, review-surface sidecars, or assumption
provenance are stale, missing, uncertain, mismatched, or otherwise flagged.
Use dashboard commands for quick paper-local diagnosis, but do not rely on a
JSON export alone when the hidden-premise lane needs Lean expansion.
Audit evidence is fail-closed. Blank template sidecars, parse failures, missing
files, missing prompt versions, stale prompt versions, missing current digests,
missing validator/model identity, missing timestamps, stale source inventories,
stale dashboard surfaces, unrecognized judgments, failed judge runs, and items
without explicit success verdicts are all alarms. The audit should move from
pending/failing to passing only after a current run records the exact version,
inputs, validator metadata, and recognized success judgment for the current
Lean and paper source.
For public-facing closeout, this includes an explicit current
`audit/review_surface_llm.json` pass even when the dashboard has 30 or fewer rows; the
30-row threshold is an early workflow prompt, not a closeout exemption.

At a statement-review boundary, run the independent LLM statement workflow:

1. Curate `PaperInterface.lean` to the paper-facing Lean definitions and named
   statements that should actually be formalized.
   If the dashboard has more than 30 rows, run a separate no-paper-context LLM
   review-surface audit and save `audit/review_surface_llm.json`; if it has 50 or
   more rows, treat that as an oversized-surface warning and curate before broad
   human review.
2. Ask a separate LLM, with no paper context, to translate each current Lean
   statement into paper-style LaTeX/prose. Save stable outputs in
   `audit/lean_to_tex_llm.json`. New tracked entries should use
   `{ "tex_statement": "...", "lean_statement_sha256": "..." }` so stale
   translation drafts can be detected, and the sidecar should record
   `prompt_version: "lean-to-tex-v3-strict-context-free-semantic-inputs"`. The translation
   prompt must require every visible binder, hypothesis, domain condition,
   named predicate/wrapper application, equivalence or implication direction,
   and conclusion to survive unchanged in the prose/LaTeX rendering. It must
   not turn a named premise into a theorem label, source-like phrase, or
   proof-route summary.
3. Ask an independent semantic LLM judge, with no Lean/proof context, to compare
   the original paper statement against the translated LaTeX/prose. Save verdicts and reasons in
   `audit/statement_match_llm.json`, including current Lean, paper, and TeX statement
   digests plus validator/model metadata, and record
   `prompt_version: "statement-match-v10-semantic-fidelity-seat-stopping"` for
   compatibility with the established v10 gate. That identifier is a version
   label, not a source-scope or domain classifier; new fidelity-risk records
   use the domain-neutral v3 execution schema. The judge must compare the full
   source statement semantically, not just the theorem
   label, qualitative claim, phrase overlap, or source-looking Lean name. It
   should expand or otherwise inspect named predicates/wrappers enough to decide
   whether every Lean premise is source-backed or derived. It should reject or
   mark uncertain any omitted subpart, added non-source hypothesis, hidden
   strengthening inside a named predicate, changed quantifier/domain, changed
   constant or normalizer, sign error, inequality-direction change, broad
   aggregate row, source-row package, certificate/replay/process/bridge
   package, or weakened/strengthened theorem.
   Every row must also enumerate `source_obligations` and `lean_obligations`
   with explicit `parameter`/`assumption`/`conclusion` kinds, then relate them in
   `obligation_alignment`. Each Lean obligation must reference exactly one
   machine-generated signature atom with `signature_ref`; the refs must cover
   every elaborated binder and the final conclusion exactly once, and the row
   must record the current `lean_signature_sha256`. Every source obligation needs an exact locator, and
   every alignment needs an explicit mathematical `bridge_statement`. A match
   is invalid if any source conclusion is unmatched or any Lean input
   lacks a source implication/equivalence. Gap lists contain obligation ids,
   not prose. A conditional-boundary resolution may document an extra Lean
   assumption but never an unmatched/weakened source conclusion. Ledger ids and
   declaration names are routing only, never evidence.
   Every row must also carry the versioned `fidelity_risk_review` inside
   `semantic_scope_review`. Review all five dimensions from expanded source and
   Lean semantics, even when a dimension is inapplicable:
   source output arity/shape and terminal projection; nonvacuous adversarial
   action spaces with carrier, capacity, and duplicate interactions; coherent
   realization of combined candidatewise extrema with actual-runner or checked
   refinement evidence; syntactic-family cardinality versus nonempty realized
   fibers, with surjectivity before exact equality; and execution scope across
   input domains, state transitions, termination conditions, numeric
   representation, cost claims, and any bridge from local execution to the
   advertised global result.
   Each applicable match must cite source and elaborated-Lean obligation ids and
   bind its semantic evidence to a Lean conclusion. A restricted input class,
   local transition, incomplete termination argument, mismatched numeric model,
   or local work count cannot be promoted to an end-to-end or polynomial claim
   without a checked global bridge.
   Function, theorem, field, and dimension names only route this review.
4. For every displayed or source-defining formula used by a selected
   paper-facing result, verify the exact signs, constants, quantifiers,
   inequality direction, normalizing factors, domains, and hypotheses through
   that result's transparent realization evidence. An exact helper/subclaim row
   may make this dependency legible, but it is not an independent normal-scope
   obligation unless the source presents it as named theory. If the formula is
   not derived from source model primitives in Lean, it is a visible proof
   boundary for the selected result, not a completed theorem.
5. If any paper-facing theorem has a premise that is not derived in Lean,
   declare it in paper-local `Assumptions.lean`, list it in `status.json`
   `review_surface.assumption_names`, and ask a separate source-assumption
   judge to confirm that it is an explicit paper/source model assumption. Save
   this in `audit/assumption_match_llm.json`, with
   `prompt_version: "assumption-provenance-v3-semantic-exact-premise-source"`.
   Do not try to hide such a premise by making the `PaperInterface.lean` row an
   `abbrev` alias to a proof-facing theorem. The audit expands review-surface
   declarations and direct paper-local alias targets, then uses Lean-native
   `#print axioms` on paper-facing rows for transitive proof debt. Any visible
   certificate, source-row equation, external theorem, or proof-boundary witness
   still counts unless it is derived or routed through the explicit assumption
   ledger.
   If `Assumptions.lean` uses `-- audit-premise:` comments, group approval is
   not enough: every exact premise must have an `audit/assumption_match_llm.json`
   `premise_judgments` entry with a source location. Mark non-source or
   not-yet-derived premises as `partial_boundary` and keep the paper status
   partial until those premises are derived or source-matched.
   The assumption judge must decide each exact premise independently. A
   displayed formula, capacity equation, threshold identity, normalization,
   density or mass row, source-row package, certificate, witness object, or
   proof convenience is not a source assumption merely because it appears in a
   proof or can be consumed by a Lean helper. It is acceptable only if the
   source states it as an assumption or theorem condition, or if Lean derives it
   from previously validated source primitives.
   This applies equally when the premise comes from a reusable library theorem.
   A direct paper alias to a library theorem that takes a certificate, witness,
   source-row package, or external-boundary parameter is conditional unless the
   paper wrapper constructs that argument internally or exposes it as a
   validated paper assumption. Run
   `python3 scripts/audit_repository.py --library-only --library-premise-audit`
   after reusable-library edits to inventory direct certificate/source-boundary
   APIs and source-shaped reusable names; combine that inventory with the
   paper-facing `#print axioms` audit and expanded-statement review.
6. If any reviewed theorem mentions a record, certificate, replay, process,
   bridge, source-row package, or broad model predicate, generate
   `audit/source_record_audit.json` with the skill helper during active
   target-setting or to diagnose a named source-record failure, and save
   `audit/source_record_match_llm.json` with `prompt_version:
   "source-record-v10-semantic-conclusion-boundary-contract"`. Every proposition or
   unknown non-data visible input and every recursively reached record field
   input needs source evidence, a Lean derivation from paper primitives, an
   approved external boundary, or an unresolved finding. A source-looking Lean
   name or theorem label is not evidence. Once the paper is frozen for closeout,
   do not invoke the raw producer directly: the planner decides whether existing
   raw evidence is reusable, needs a judgment-only repair, or needs one
   serialized raw transition.
   A direct statement match never proves a caller-supplied conclusion-bearing
   premise or model record. A builder returning `Record` proves only that it
   can build some record, not that it equals the visible argument; retain
   field-level source evidence unless a reviewed equality/reconstruction bridge
   identifies the argument.
   The generated semantic-model lane is type-shape driven. If it marks
   `carrier_and_domain.requires_cardinality_boundary_analysis_when_detected`, the
   judgment must include `cardinality_boundary_analysis` with the source and
   Lean cardinal domains, endpoint cases checked, strictness witness/reason, and
   Lean boundary evidence. If it marks
   `joint_law_and_state_evolution.requires_transformed_law_analysis_when_detected`,
   include `transformed_law_analysis` with source/Lean operations, the full
   parameter-domain/endpoints account, normalization or pushforward evidence,
   outcome-equivariance/no-relabeling evidence, and a Lean semantic bridge. An
   explicit no-transform or no-strictness finding is still a semantic judgment,
   never an inference from a declaration name.
   Do not duplicate an ordinary visible-premise judgment when a current,
   gap-free v10 row already checks that exact declaration through a selected
   normal-scope named theorem, proposition, lemma, corollary, definition, or
   visibly source-labelled claim/condition. Standalone remarks, formulas,
   equations, algorithms, and algorithmic formulas are deep-only and cannot
   manufacture this normal-scope discharge. A selected row can cover only the
   ordinary premise surface; it never resolves a semantically identified
   conclusion dependency, including a caller-supplied record or certificate
   input. Those fields remain subject to recursive v10 inspection.
   The static lane expands parsed records through both `abbrev` and reducible
   `def` type aliases and follows imported repository records. Its data/proof
   decision uses instantiated types and `Type`/`Sort` binder kinds; renaming a
   structure, field, theorem, constructor, or generic carrier must not change
   the verdict.
   An author-approved corrected model is a distinct closeout scope, not a
   shortcut around source fidelity. Pin the approval memo and archive, set
   `archival_equivalence_claimed: false`, and bind the complete canonical
   content of every governing correction. The current source-record audit must
   enumerate the expanded semantic items, each by fully qualified declaration
   and digest. Its corrected-model semantic contract must map every such item,
   every detected dimension, every target result, and every visible model or
   assumption condition to exact generated items and qualified declarations.
   Include checkable source locators, source-vs-Lean comparisons, exact Lean
   evidence, approval evidence for nonliteral conditions, and checked bridge
   declarations present in the current imported paper-local surface. Never use
   a final component, field name, binder name, or correction ID alone as a
   match; ambiguity or staleness fails closeout.
   Recursive traversal must also preserve function direction. A proposition
   stored in a record or returned by one of its fields is package evidence; a
   proposition inside the exact source-step object accepted as an argument to
   a record method is a caller-supplied antecedent. Do not classify that nested
   argument as a stored result merely because one of its constructor fields is
   syntactically equal to a component of the reviewed row's conclusion.
   A certificate that is constructed internally from already proved primitives
   is discharged; a certificate that is merely consumed by a helper remains a
   premise of every paper-facing theorem that depends on that helper.
   Compare visible proposition premises structurally with each theorem's
   advertised result. A supplied premise equivalent to, providing, or logically
   composing advertised feasibility, cost, runtime, or optimality is
   conclusion-bearing proof debt and cannot cover that same source theorem,
   regardless of declaration or binder names.
   Apply the same five fidelity-risk checks to boundary records and helper
   premises. In particular, an adversarial universal can be vacuous after a
   validity filter, independent per-candidate extrema may have no joint witness,
   and a syntax-level family count is not the number of nonempty semantic fibers
   without a surjectivity theorem.
   Audit algorithmic complexity from the executable's transitive semantic
   operational dependency graph across every branch reachable over the claimed
   input domain. Extensional or refinement correctness does not transfer a
   runtime bound. A cached or memoized executor must expose that no reachable
   recursive branch evaluates the old semantic closure or oracle after
   materialization; function and declaration names are routing only, not
   evidence. Charge traversal and enumeration length, duplicates,
   materialization/rebuilding, representation and container primitives, and
   exact-rational bit growth. Any excluded item requires withholding the
   corresponding full runtime match. Also require a worst-case recurrence or
   equivalent bound over all reachable branches. When eliminating closure
   recomputation is material, require a cost-threaded executor or generated
   IR/C evidence pinned by source and artifact digests to the exact audited
   build, with a semantic source binding; absence of a symbol name is not
   evidence after renaming or inlining.
   An exact `matches` judgment at `polynomial_time` must include
   `operational_complexity_review.schema_version:
   "operational-complexity-review-v1-transitive-work-accounting"`. The
   dashboard rejects a missing review, incomplete reachable-branch graph,
   missing worst-case recurrence or bound, unpinned material closure evidence,
   and any work item marked `missing` or `excluded_by_claim`.
   For a repaired source defect or a claim whose correctness depends on an
   executable/runtime, preprocessing, counterexample, or refinement bridge,
   opt the source map into `semantic_contract_schema: 1`. Mark the item
   `claim_bearing: true`, classify every other map item explicitly as true or
   false, and give each true item `semantic_contract` with a reviewed transparent
   Prop specification (`spec_declaration`), a reviewed theorem/lemma
   (`evidence_declaration`), `evidence_mode: proves|refutes`, and
   `semantic_shape: plain`. The full audit asks Lean Meta whether the evidence
   has exactly the specification, or exactly its negation. Specialized runtime,
   preprocessing, and refinement shape labels are rejected until the audit has
   a real structural check for them; declaration names never relax the exact
   proposition check. Link each
   `repaired_in_lean` fidelity-ledger defect by its stable id through
   `source_defect_ids`. A new-paper `by sorry` statement is an audited target
   skeleton, not proof evidence, so do not manufacture a semantic contract from
   that theorem alone.
   For every new or explicit-v11 full closeout, this exact-proposition route is
   necessary but not sufficient: complete the general v11
   source-to-Spec correspondence described above. It applies to every
   claim-bearing endpoint, not only runtime, preprocessing, counterexample, or
   refinement claims. Independently inventory pinned source atoms before Lean;
   then account for the full elaborated closure, including proof and instance
   arguments, without any name or container-based exemption. V10 sidecars and
   contracts remain readable historical evidence but are not v11 credit.
   `claim_bearing` still serves ordinary named-theory coverage: a selected
   source definition can correctly retain `claim_bearing: true` without being
   a v11 theorem-realization target. Do not invent a `Prop` specification or
   semantic contract for such vocabulary merely to satisfy v11; strict
   source-to-Spec records belong to theorem-like source claims.
   For a named evidence-integrity diagnosis during evidence review, run
   `python3 scripts/audit_evidence_integrity.py --paper <paper> --include-source-obligations`.
   This opt-in lane reports current `unresolved_assumed_math` source-record
   judgments under the current audit digest and ignores stale historical
   judgments, so the remaining proof queue is semantic rather than name-based.
   It is not a routine frozen-closeout precursor; the planner-issued strict
   worker runs the acceptance lane in-process.
   Keep event semantics exact: open/strict events (`>`, `Ioi`, strict upper
   tails) are not interchangeable with closed/non-strict events (`>=`, `Ici`)
   unless Lean proves the boundary has zero mass or the source explicitly
   supplies that regularity. A distributional quantile or bracket lemma with a
   closed-tail lower side is not evidence for a strict-tail lower bound by
   naming similarity.
7. Treat any formula wrappers as dependency visibility, not proof provenance
   or automatic normal-scope inventory. A paper-facing `_formula`, `_iff`,
   `_rule`, or analogous row, when used, is closed only
   when the equality/iff/rule is proved from the source model primitives or from
   separately validated paper assumptions. A wrapper whose body assumes a
   displayed equation, source row, capacity identity, normalization, or other
   formula is a partial endpoint until that assumption is eliminated or
   validated as a paper assumption.

If the semantic judge reports mismatch or uncertainty, edit the Lean statement and
repeat the translation/judgment pass unless the translation itself is plainly
wrong. The dashboard displays the paper statement, current Lean statement,
Lean-to-TeX draft, and independent LLM judgment; these LLM checks do not count
as human review rows. `python3 scripts/review_dashboard.py --paper <paper> --precheck`
reports missing, stale, uncertain, and mismatched LLM statement-audit rows and
assumption-provenance rows separately from human dashboard-review entries. Use
it to diagnose an active statement-review problem, not as a routine
frozen-closeout predecessor.
If every row, or nearly every row, is uncertain, treat that as a parser or
source-statement extraction failure first. Fix the source map/report sections,
or record one paper-wide source-map issue, before accepting row-by-row
uncertainty.

When updating evidence, refresh the machine-readable validator ledger with:

```bash
python3 scripts/review_dashboard.py --paper <paper> --export-format validators-md
```

The JSON ledger should include every dashboard/PaperInterface row, human/model/
agent validators, and validator comments. It is provenance for statement
targets, not a replacement for the human-only dashboard review count. Keep it
in the public audit JSON and bind it through the canonical closure receipt,
rather than appending it to the final report.

For a non-interactive statement-review check (exits non-zero when anything is
stale or unreviewed):

```bash
./review-dashboard.sh --check
```

This is diagnostic/review preparation; it does not replace the planner-issued
strict closeout receipt.

If you are working in an older paper folder that already has
`PaperInterface.lean` but no local launcher yet, run once:

```bash
python3 scripts/bootstrap_review_launchers.py --write
```

## Maintenance Note

Use the narrowest focused paper build that exercises the active proof seam.
Repository-wide builds belong to release or integration milestones, not routine
paper closeouts. If a private paper thread temporarily breaks an aggregate
build, document the exact blocker in its private status rather than inferring
anything about unrelated paper audits.
