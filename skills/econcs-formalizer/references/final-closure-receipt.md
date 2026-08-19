# Final Closure Receipt

`FINAL_CLOSURE_RECEIPT.md` at a paper root is the only canonical paper-local
closure artifact. It is a compact, human-readable receipt with TOML front
matter designed for mechanical validation. `FINAL_VALIDATION_REPORT.md`
states the mathematical verdict; audit sidecars, source records, direct-review
ledgers, and planner/worker files are inputs. None of those files is itself a
second final receipt.

Create this file only after the paper has a frozen successful closeout. Do not
backfill it just to make historical documentation look current. Migrate a
previously completed paper at its next deliberate closeout or release boundary.

## Required form

Use this exact shape. Replace every angle-bracket value; omit a lane-inapplicable
field rather than inventing a placeholder.

````markdown
+++
schema = 2
paper = "<PaperRoot>"
closure_status = "current"
evidence_lane = "<raw-source-record or direct-source-row-review>"
closed_at = "YYYY-MM-DD"

[source_artifact]
path = "papers/<PaperRoot>/<source path>"
sha256 = "<pinned source bytes>"

[statement_map]
path = "papers/<PaperRoot>/audit/paper_statement_map.json"
sha256 = "<current bytes>"

[paper_interface_closure]
root = "PaperInterface.lean"
sha256 = "<current transitive import-closure identity>"

[review_ledger]
path = "papers/<PaperRoot>/<direct semantic review ledger>"
sha256 = "<current bytes>"
# Required when this is FINAL_VALIDATION_REPORT.md. The receipt binds the
# detailed evidence tail, not editable Sections 1--11.
content_start = "## 12. Detailed Formalization Evidence"

# Required only for raw-source-record.
[raw_source_record]
path = "papers/<PaperRoot>/audit/source_record_audit.json"
sha256 = "<current bytes>"

[focused_build]
command = "env LEAN_NUM_THREADS=1 lake build <PaperRoot>"
target = "<PaperRoot>"
result = "passed"
commit = "<frozen Git commit>"

[protocol]
formalization_review_protocol_sha256 = "<current protocol identity>"
+++

# Final Closure Receipt
````

One short paragraph below the block may explain a real source-paper caveat or
why the direct-review lane was used. Do not add command transcripts, retry
history, source-row prose, or unpinned claims of review. The linked review
ledger remains the place for row-level reasoning.

## Evidence lanes

Use `raw-source-record` for the ordinary current machine source-record route.
It requires a current raw record and a direct semantic-review ledger.

Use `direct-source-row-review` only when the protocol or user explicitly
selects this lane. It requires a current, source-anchor-based ledger covering
the normal selected scope, a current `PaperInterface` closure, and the focused
build. It does **not** require a replacement raw scan merely because a prior
machine record is historical. It is never inferred from a final report alone.
For a v11 source-Spec closeout, that ledger is exactly
`audit/v11_raw_source_spec_screening.json`, not a validation report or an
arbitrary summary. The integrity gate separately verifies its complete
one-source-claim/one-direct-Spec coverage, raw source and Spec hashes, and
`matches` verdicts. It also verifies current source-to-library review for every
material reusable declaration on that selected Spec surface.

Both lanes require the exact current source, statement map, interface closure,
review ledger, protocol, and successful focused build shown above. A receipt
that cannot bind each applicable item is not current. When the review ledger
is `FINAL_VALIDATION_REPORT.md`, bind its detailed-evidence section beginning
at `## 12. Detailed Formalization Evidence`; the human-facing front matter is
not itself a receipt input.

## Refresh rule

Invalidate and replace the receipt once after any of these changes:

- selected source bytes or source route;
- statement map or normal-scope selection;
- transitive `PaperInterface` closure;
- selected reviewer ledger or evidence-lane semantics;
- focused build target or a failed/repaired focused build; or
- a semantic protocol change affecting this receipt's lane.

Do **not** refresh it merely because aggregate status files, site rendering,
human-report wording, ignored worker traces, timing diagnostics, or a
registered `review_compatible` audit-engine transition changed. If a change is
ambiguous, stop and classify it before writing a replacement.

Always complete all material edits first, run the selected evidence lane and
focused build on the frozen inputs, then write this one file once. A receipt is
not authorization to skip a required proof, source review, or release check.
