# Independent Audit Guide

Updated: 2026-07-31

`config/formalization_audit_protocol.json` is the normative machine-readable
policy for current audit versions, normal/deep scope, semantic reuse, and build
selection. This guide defers to it whenever historical sidecar labels or prose
conflict.

This guide describes how to audit a public paper folder without private
repository context.

## 1. Start From The Paper README

Open `papers/<Paper>/README.md`. It should list:

- final status;
- paper reference;
- lines of Lean code;
- compact Lean interface;
- final validation report;
- dependency DAG;
- source/status JSON and available audit sidecars.

Read `PaperInterface.lean` first. It is the only supported row-level dashboard
and LLM-as-judge surface. A separate `AuditInterface.lean` may contain proof
support or compatibility wrappers, but it is not the configured human-review
surface.

## 2. Read The Final Validation Report

Open `FINAL_VALIDATION_REPORT.md` and check the top summary:

- completion status;
- Lean build status and Lean lines of code;
- source-coverage audit status;
- statement-match audit status;
- assumption-provenance audit status;
- source-record audit status;
- holistic source-first and DAG/source-json audit status;
- known assumptions, caveats, proof deviations, and gaps;
- human dashboard review status.

The validation report is the human-facing summary. Raw machine ledgers may be
kept in tracked JSON sidecars instead of repeated in full in the report.

## 3. Compare Source Claims To The Review Surface

Inspect `audit/paper_statement_map.json` when present. It may retain a broad
source-first inventory for traceability, but normal
`named_theoretical_statements` coverage selects independently source-presented
named definitions, theorems, lemmas, propositions, corollaries, theorem-like
claims, and explicitly named source conditions/models. Standalone formulas,
equations, algorithms, examples, figures, captions, simulations, empirical
claims, and computational results are independent obligations only in the
explicit deep all-prose mode. They remain relevant when a selected named result
depends on them.

Then inspect the configured review surface:

```bash
python3 scripts/review_dashboard.py --paper <Paper> --export-format md
```

or run:

```bash
python3 scripts/review_dashboard.py --paper <Paper> --precheck
```

These are read-only independent-audit diagnostics. They are useful for
inspection or a named dashboard failure, but are not a required prelude to a
frozen closeout; Section 6's planner route owns the accepting transaction.

The review rows should correspond to source claims, explicit source assumptions,
or clearly documented support-only proof-route material.

## 4. Check The Lean Statements

Read `PaperInterface.lean` for the compact entrypoint. If a status file or
sidecar appears to route review rows through `AuditInterface.lean` or another
implementation module, treat that as a workflow error to repair before judging
the paper. Implementation modules may support proofs, but every audited
paper-facing row must be declared in `PaperInterface.lean`; only auxiliary
aliases may be exported there.

For each audited row, compare:

- source statement text and source location;
- Lean declaration statement;
- Lean-to-text translation when available;
- statement-match judgment;
- assumption-provenance judgment for visible premises;
- final-report notes for boundaries or source corrections.

Do not treat theorem labels, similar names, or proof-route wrappers as enough
evidence. Check hypotheses, domains, constants, normalizations, inequality
directions, quantifiers, and conclusions.

## 5. Check LLM Audit Sidecars

The common sidecars are:

- `audit/lean_to_tex_llm.json`;
- `audit/statement_match_llm.json`;
- `audit/assumption_match_llm.json`;
- `audit/paper_statement_map.json`;
- `audit/paper_coverage_llm.json`;
- `audit/review_surface_llm.json`;
- `audit/source_record_audit.json`;
- `audit/source_record_match_llm.json`.

Sidecars should include schema or prompt version, validator identity, timestamp,
source or statement digests, verdicts, reasons, and source evidence where
applicable. Treat missing, stale, uncertain, or mismatch rows as audit findings
to resolve or document.

For current v10 statement judgments, inspect the semantic obligation ledger
rather than declaration names. A separately numbered declaration-manifest
schema is a serialization detail, not an audit-version label. Every source
obligation needs an exact locator; every alignment needs an explicit
mathematical equivalence or implication; every source conclusion and Lean
assumption must appear in the exact gap accounting. An accepted conditional
boundary can explain an extra Lean assumption, but an unmatched source
conclusion is a weakened theorem and remains a blocker. New or materially
reissued closeouts additionally require the normative v11 theorem-realization
correspondence.

## 6. Run The Repository Checks

For a targeted paper closeout, freeze the reviewed inputs and begin with the
planner:

```bash
python3 scripts/closeout_reuse_plan.py --paper <Paper>
```

Execute only the current `next_action`; when it schedules strict closeout, use
the exact identity-addressed `run_paper_closeout.py` command it prints. Its
worker runs the focused evidence-integrity and conclusion-provenance acceptance
lanes in-process after the primary paper gate passes. It stops at an earlier
failing stage and shares exact current source-record/Lean identities across
stages.

For a named failure diagnosis only, the underlying audit may be run without
creating a competing closeout execution record:

```bash
python3 scripts/audit_repository.py --paper <Paper> --paper-closeout --include-active --info-limit 0 --no-closeout-state
```

That direct command is non-accepting; a passing result does not replace the
planner-issued receipt. Standalone component commands are likewise for diagnosis
or explicit release certification, not mandatory reruns after an unchanged
passing closeout.

For dashboard checks:

```bash
python3 scripts/review_dashboard.py --paper <Paper> --statement-check
python3 scripts/review_dashboard.py --paper <Paper> --paper-coverage-check
python3 scripts/review_dashboard.py --paper <Paper> --source-to-lean-check
python3 scripts/review_dashboard.py --paper <Paper> --assumption-check
```

For independent Lean proof checking, run the paper build target listed in
`status.json` when a current strict receipt is unavailable or a named build
failure needs diagnosis. Do not repeat it after an unchanged planner-issued
closeout merely to recreate a second acceptance signal.

## 7. Interpret The Result

A clean audit means the repository artifacts are internally consistent and the
tracked audit lanes are current. It does not replace human judgment about
whether a paper statement was translated exactly. Independent audit comments
should identify the source claim, Lean row, sidecar judgment, and proposed
resolution.
