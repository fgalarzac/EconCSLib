# Final Validation Report: [Paper Short Name]
Updated: YYYY-MM-DD

## 1. Human Verdict
Not started. No formalization or paper-correctness assessment has been
completed yet, and no human dashboard sign-off has been recorded.

## 2. Closeout Status
- Completion status: not formalized
- One-sentence recap: Scaffold only.
- Human review: not yet recorded.

## 3. Source and Scope
- Paper: <title>
- Source version: <arXiv/publisher URL + version/date>
- Formalized paper surface: <named definitions/results, or `None yet`>
- Scope boundary, if any: <paper-facing boundary, or `None`>

Keep Sections 1--11 in paper language. Do not put file paths, Lean declaration
names, implementation representations, audit row counts, source hashes,
commands, build logs, or prior-proof history in this report. Put technical
validation detail in public audit JSON and the canonical closure receipt.

## 4. Researcher Summary of Checked Results
None yet. Summarize checked paper definitions and named results here in paper
language.

## 5. Remaining Boundaries and Gaps
All named results remain open. Put partial-formalization, external-library,
analytic, solver, runtime, or source-certificate boundaries here, not in the
additional-assumptions section.

## 6. Additional Assumptions Beyond Paper
None.

Only list hypotheses added by the formalization that are not paper assumptions
or source theorem conditions. If a dependency is open formalization work rather
than a hypothesis, describe it in Section 5. A central endpoint that needs an
added non-source assumption is partially formalized even if the restricted
theorem is proved; do not use `formalized with caveat` for that limitation.

## 7. Proof-Strategy Deviations
None.

Use this section only for a substantive mathematical departure from the source
proof. Do not record Lean implementation choices, model representations,
helper constructions, or workflow history.

## 8. Proof Tricks Worth Reusing
None.

## 9. Generalizations, Conjectures, and Extensions
None yet. After the source theorem chain is stable, record trivial or
near-trivial weakened assumptions, immediate corollaries, stronger conclusions,
source conjectures that can now be proved cheaply, or extension ideas to defer.

## 10. Source Clarifications and Exact Readings
None found.

Use this section for a material source clarification or, only when necessary,
a demonstrably false printed formula or statement. State the present
mathematical reading and result-level effect without narrating earlier repair
work. Ordinary proof engineering choices and open Lean/library work do not
belong here. A clarification with an unchanged substantive advertised endpoint
remains compatible with `formalized` and uses `status_impact: formalized_note`
in the source-proof fidelity ledger.

## 11. Paper Issues or Caveats
None.

Reserve this section's status-bearing caveats for a substantial error in a
central source-paper claim whose current mathematical endpoint is fully proved.
Such an issue uses `status_impact: formalized_with_caveat` and explains why the
difference is substantive. Put weaker/narrower Lean targets and non-source
restrictions in Sections 5--6 under partial status instead.
