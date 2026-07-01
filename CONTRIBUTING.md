# Contributing to EconCSLib

Draft policy: this contribution process is provisional while EconCSLib is being
prepared for public release. If you want to contribute, please contact Nikhil
Garg at ngarg@cornell.edu before starting substantial work.

If you are starting from the public repository and do not already have a
private EconCSLib workspace, begin with
[`docs/NEW_CONTRIBUTOR_WORKFLOW.md`](docs/NEW_CONTRIBUTOR_WORKFLOW.md). It
describes the private-workspace-then-pull-request workflow, how to start a new
paper, and when to publish a clean public review branch.

For the current paper-formalization workflow, also read:

- [`docs/paper-formalization-quickstart/README.md`](docs/paper-formalization-quickstart/README.md)
  for the short contributor-oriented start path;
- [`docs/AGENT_FORMALIZATION_WORKFLOW.md`](docs/AGENT_FORMALIZATION_WORKFLOW.md)
  for the source-inventory, proof, audit, and closeout workflow;
- [`docs/PAPER_COVERAGE_AUDIT.md`](docs/PAPER_COVERAGE_AUDIT.md) for the
  source-paper-to-Lean coverage audit lanes; and
- [`docs/REVIEW_DASHBOARD.md`](docs/REVIEW_DASHBOARD.md) for human and
  LLM-as-judge statement-review expectations.

EconCSLib has two connected goals:

- maintain a reusable Lean library for economics and computation; and
- maintain source-faithful, auditable formalizations of individual papers.

The public repository should contain reusable library code, tooling, docs, and
completed paper formalizations. Partially formalized papers may be developed in
private workspaces until their authors are ready to make them public.

New contributors should not work directly on the public repository. Use a
private local clone or private collaboration space first, then open a pull
request containing only public-safe changes.

In some cases, unfinished work may intentionally be made public as a documented
partial formalization, as with current public partials in this repository. That
should be an explicit project decision, not the default path for new paper
work.

## What To Contribute

Contributions are welcome in two main categories.

### Reusable Library Updates

Library contributions belong under `EconCSLib/`. These should be
paper-independent definitions, lemmas, theorem interfaces, or proof tools that
could plausibly be reused by more than one economics-and-computation
formalization.

Good candidates include probability primitives, optimization certificates,
matching and auction abstractions, finite expectation lemmas, stochastic-process
tools, asymptotic helpers, and reusable theorem wrappers.

Library pull requests may be submitted before the motivating paper
formalization is public, provided the contribution is self-contained and does
not reveal private or unfinished paper material.

### Completed Paper Formalizations

Paper contributions belong under `papers/<PaperName>/`, where `<PaperName>`
uses the existing citation-style convention, for example
`MSVV07AdWords` or `Roth82StableMatching`.

A completed paper contribution should include:

- `README.md`
- `FORMALIZATION_PLAN.md`
- `review-dashboard.sh`
- `MainTheorems.lean`
- `PaperInterface.lean`
- `Assumptions.lean` when source assumptions or source conditions are exposed
- `status.json`
- `docs/DependencyDAG.tex`
- `docs/DependencyDAG.pdf`
- `docs/FINAL_VALIDATION_REPORT.md`
- `AGENT_SOURCE_AUDIT.md`
- `audit/paper_statement_map.json`
- `audit/paper_coverage_llm.json`
- `audit/lean_to_tex_llm.json`
- `audit/statement_match_llm.json`
- `audit/assumption_match_llm.json` when assumptions or source conditions are
  exposed
- any needed implementation modules
- a passing Lean build target for the paper

`PaperInterface.lean` should be the compact human-facing surface: source
definitions and named theorem statements in paper order. Put broad proof
plumbing, helper endpoints, and implementation detail in `MainTheorems.lean`,
`ProofInterface.lean`, or lower paper-local modules.
Keep the paper-local `status.json` as the source of truth for review rows,
artifact paths, and public status, then regenerate `papers/status.json`.

## Private Workflows For Unfinished Papers

If a paper is not ready to be public by default, develop it in a private
repository or private clone. Keep the full working history there.

When the paper is complete, or when the project explicitly decides to publish a
documented partial formalization, publish only the paper folder and any reusable
library updates that are ready for public review. If you want to preserve
development history, prefer a private repository dedicated to that paper. That
makes it possible to publish a filtered or subtree history later without
exposing unrelated unfinished work.

Do not rely on a private branch inside the public repository to hide unfinished
work. Public GitHub repositories do not provide private per-branch visibility,
and public forks are public.

## Pull Request Expectations

Before opening a pull request:

- keep imports as narrow as practical;
- avoid `sorry`, `admit`, new top-level `axiom`s, or `unsafe` declarations;
- run the relevant targeted `lake build` command;
- update the paper README, dependency DAG, validation report, paper-local
  `status.json`, and audit sidecars when changing a paper-facing theorem
  status;
- keep source-paper caveats and additional assumptions explicit in theorem
  statements and ledgers; and
- avoid mixing unrelated paper work into a library PR.

Unless explicitly marked otherwise, contributions intentionally submitted for
inclusion in EconCSLib are accepted under the Apache License, Version 2.0. This
repository license covers the Lean code, scripts, documentation, and site
source; it does not grant redistribution rights for third-party source-paper
PDFs or extracted text caches.

For reusable library changes, a typical validation command is:

```bash
lake build EconCSLib.Foundations
python3 scripts/audit_repository.py
```

For paper changes, build the paper target, for example:

```bash
lake build Roth82StableMatching
```

For a paper PR that claims a public status such as `formalized` or
`partially formalized`, also run the current review and coverage gates:

```bash
python3 scripts/review_dashboard.py --paper <PaperName> --statement-check
python3 scripts/review_dashboard.py --paper <PaperName> --source-to-lean-check
python3 scripts/review_dashboard.py --paper <PaperName> --assumption-check
python3 scripts/audit_repository.py --paper <PaperName> --paper-closeout --include-active --info-limit 0
python3 scripts/sync_paper_status.py --check
```

If a gate fails because an audit sidecar is missing, stale, or uncertain, treat
that as a failed audit until the source-grounded judgment is rerun and recorded
or the paper status is downgraded to describe the missing boundary.

The full target is desirable before release-oriented merges:

```bash
lake build EconCSLib
```

## Pull Request Checklist

- [ ] This pull request is either a reusable-library change or one completed
      paper formalization.
- [ ] `lake build <target>` passes for the changed library or paper.
- [ ] Paper theorem-status rows use the vocabulary in `docs/STATUS.md`.
- [ ] `PaperInterface.lean` exposes the human-facing theorem statements.
- [ ] `audit/paper_statement_map.json` was built or checked from the source
      paper itself, not from Lean declaration names.
- [ ] `audit/paper_coverage_llm.json` confirms every in-scope source item is
      covered by current dashboard rows or is explicitly marked conditional,
      support-only, or out of scope.
- [ ] `audit/statement_match_llm.json` and, when applicable,
      `audit/assumption_match_llm.json` are current for the paper-facing rows
      and source assumptions.
- [ ] `AGENT_SOURCE_AUDIT.md` records an independent source-first holistic
      audit that does not merely summarize existing sidecars and checks for
      omissions, hidden strengthening/weakening, and semantic mismatches.
- [ ] Caveats and source-proof deviations are documented in the paper README or
      `docs/FINAL_VALIDATION_REPORT.md`.
- [ ] `python3 scripts/sync_paper_status.py --check` passes after generated
      status files, docs tables, README rows, and site rows are refreshed.
- [ ] Source PDFs, extracted source-paper text caches, rendered local PDFs,
      dashboard caches, and other ignored local artifacts are not added to Git.

## Review Standard

Lean verifies proofs relative to the formal statements, imports, and
assumptions. Human review is still required to check that the Lean statements
faithfully represent the source paper.

For paper formalizations, reviewers should be able to start from:

1. `docs/FINAL_VALIDATION_REPORT.md` or the validation summary;
2. `PaperInterface.lean`;
3. `docs/DependencyDAG.tex`; and
4. `README.md`.

If those files do not clearly state what was proved and what assumptions
remain, the paper contribution is not ready to merge.

The current audit standard checks both directions. First, a source inventory
from the paper must map each in-scope source definition, example, remark,
proposition, theorem, corollary, and theorem-like displayed claim to one or
more Lean review rows. Second, each Lean review row and each exposed source
assumption must be judged against the source statement or source primitive it
claims to represent. The holistic `AGENT_SOURCE_AUDIT.md` is a separate
source-first review pass over the paper and Lean interface; it is not a
substitute for the machine-readable sidecars, and the sidecars are not a
substitute for that holistic pass.
