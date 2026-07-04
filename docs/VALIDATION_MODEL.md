# Validation Model

Updated: 2026-07-04

EconCSLib separates three questions that are easy to conflate.

## 1. What Lean Checks

Lean checks that the formal proof terms establish the displayed Lean theorem
statements from the imported library declarations and explicit theorem
hypotheses. A successful Lean build is therefore evidence about the formal
statements in the repository.

Lean does not, by itself, decide whether a theorem statement is the right
translation of a source-paper statement.

## 2. What Human Review Checks

Human statement review is the review path for the source-to-Lean translation
boundary. A reviewer compares a source-paper definition, formula, theorem, or
subclaim against the corresponding Lean statement and records a dashboard
judgment.

Human-review records should identify the reviewer, timestamp, source statement,
Lean declaration, verdict, and notes. Public counts should be read as counts of
saved dashboard judgments, not as a general claim that a whole paper has been
independently reviewed.

## 3. What LLM Audit Checks

LLM-as-judge passes are audit evidence. They help find missing source claims,
hidden theorem premises, stale row mappings, mismatched formulas, and review
surface problems. The standard lanes are:

- Lean-to-text translation from the Lean statement alone;
- source-vs-translation statement matching;
- assumption-provenance matching;
- source-inventory-to-dashboard coverage;
- recursive source-record and boundary-input classification;
- holistic source/DAG/source-json comparison.

These lanes are intentionally separate. Row-local statement matching cannot
establish paper coverage, and source-coverage matching cannot establish that
each Lean row has the exact same hypotheses and conclusion as the source.

LLM audit status should report `missing`, `stale`, `uncertain`, `mismatch`,
`conditional_boundary`, and related statuses directly. Those statuses are not
human review and should not be counted as human dashboard sign-off.

## 4. Public Status Reading

Read public paper status as:

- `Formalized`: Lean proves the exposed paper endpoints under the displayed
  Lean statements, with no known theorem-level mathematical boundary recorded
  in the public status.
- `Formalized with caveat`: Lean proves the exposed endpoints, but the paper
  has a documented source correction, source ambiguity, or caveat that matters
  to the theorem statement.
- `Partially formalized`: some paper endpoints are Lean-checked, but known
  source claims, assumptions, or theorem-level proof work remain open.
- `Human review`: saved dashboard rows reviewed by a human.
- `LLM audit`: tracked machine-readable sidecars checking statement matching,
  coverage, assumption provenance, source records, and holistic coverage.

No single column is a complete trust label. The final validation report should
give the combined status in plain language.
