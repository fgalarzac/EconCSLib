# Formalization Notes

This file preserves the previous hand-written paper-folder README content.
The GitHub-facing `README.md` is now a generated status overview.

# Simpler Than You Think: The Practical Dynamics of Ranked Choice Voting

## Source Version

- Paper: *Simpler Than You Think: The Practical Dynamics of Ranked Choice Voting*
- Authors: Sanyukta Deshpande; Nikhil Garg; Sheldon H. Jacobson
- Version formalized: arXiv:2602.14329; Journal of Computational Social Science 2026
- Official URL: https://link.springer.com/article/10.1007/s42001-026-00470-7
- Public PDF: https://arxiv.org/pdf/2602.14329.pdf

The PDF is cached locally as `source.pdf` and ignored by Git. The extracted text
cache is `source.txt` when `pdftotext` succeeds, and is also ignored by Git in
public workspaces unless redistribution rights have been checked separately.

## Paper-Facing Ledger

- Implementation theorem file: `DGJ26PracticalDynamicsRCV/MainTheorems.lean`
- Human-facing theorem file: `DGJ26PracticalDynamicsRCV/PaperInterface.lean`
- Machine-readable status source: `DGJ26PracticalDynamicsRCV/status.json`
- Outside-Lean proof plan: `DGJ26PracticalDynamicsRCV/docs/FORMALIZATION_PLAN.md`
- Final validation report: `DGJ26PracticalDynamicsRCV/FINAL_VALIDATION_REPORT.md`
- Next-agent starting point: `DGJ26PracticalDynamicsRCV/docs/START_HERE_NEXT_AGENT.md`
- Stopping-point handoff: `DGJ26PracticalDynamicsRCV/HANDOFF_2026-06-29_STOPPING_POINT.md`
- Dependency DAG: `DGJ26PracticalDynamicsRCV/docs/DependencyDAG.tex`
- Rendered DAG: `DGJ26PracticalDynamicsRCV/docs/DependencyDAG.pdf`

`PaperInterface.lean` should be readable on its own: expose source formulas and
direct theorem statements there, with short proofs that call into
`MainTheorems.lean`. Do not mark a row `formalized` unless the Lean declaration
is closed and the remaining assumptions cell is `None`.
Keep the dashboard surface small: one row per paper-facing definition or named
result, not every helper theorem, certificate, or proof-route alias.

Use the controlled status vocabulary from `../../docs/STATUS.md`. Public-facing
rows should use `partially formalized` for results that still depend on an
external theorem, certificate, or proof boundary, and should name that boundary
in the final column rather than using `conditional` as a separate status label.
Keep theorem/table content synchronized with `DependencyDAG.tex` node styles and
`MainTheorems.lean` declarations before marking a row `formalized`. Keep
`status.json` as the source of truth for review rows, artifact paths, and the
paper's top-level public status.

At the start of the paper, fill in the `FORMALIZATION_PLAN.md`
`Initial Outside-Lean Paper Audit` section before deep proof work. Read the
source, sanity-check every named result and formula-bearing displayed claim for
signs, constants, normalizations, quantifiers, domains, and dependencies, and
record suspected bugs, missing assumptions, formula ambiguities, and proof
strategy consequences. The initial plan is a hard start gate: include the
source/version inventory, complete named-result ledger, formula/dependency
sanity pass, shared-library reuse checkpoint, and formal target/boundary map
before serious theorem proving. Alert the user early about any major issue.
After that source inventory and the first compact `PaperInterface.lean`
skeleton exist, run the smaller statement target-setting pass: populate
`lean_to_tex_llm.json`, populate `statement_match_llm.json`, and run
`python3 scripts/review_dashboard.py --paper DGJ26PracticalDynamicsRCV --statement-precheck`.
Also populate `paper_statement_map.json` for the paper's source definitions,
formulas, and named claims, then run the paper-level coverage pass and save
`paper_coverage_llm.json`: this asks whether every source statement that should
be represented is covered by at least one dashboard row. This source-to-row
accounting is separate from the row-local statement judge.
Then run `python3 scripts/review_dashboard.py --paper DGJ26PracticalDynamicsRCV
--assumption-precheck`: the statement judge is row-local and does not certify
that theorem premises are source assumptions or derived facts. Use this pass
only to correct theorem targets and premise provenance; do not update the DAG,
final validation report, human-review log, or review-surface audit just because
this early check ran.

At review boundaries, populate `lean_to_tex_llm.json` with context-free
Lean-to-TeX/prose translations generated from `PaperInterface.lean` alone. The
translator must preserve every visible variable, binder, hypothesis, domain
condition, equivalence direction, and conclusion; it must not summarize a theorem
as an endpoint label or omit conditions that appear in the Lean statement. New
tracked entries should use `{ "tex_statement": "...", "lean_statement_sha256":
"..." }`. Then populate `statement_match_llm.json` with an independent
no-context judgment of whether each translation matches the original full paper
statement, including all hypotheses, subparts, quantifiers, domains, constants,
normalizations, signs, inequality directions, and conclusions. A row may be
judged `matches` only if it is equivalent to the full source statement or to a
clearly identified source subpart; if the Lean translation is a conditional
wrapper, source-row package, omitted subclaim, weakened/strengthened statement,
or broad aggregate for several displayed formulas, the judge must mark
`mismatch` or `uncertain`. Include Lean, paper, and TeX statement digests plus
the judge model/agent name, validator type, validation timestamp, and any
validator comment. If the judge flags a mismatch or uncertainty, iterate on the
Lean statement before treating it as the paper theorem target. Run
`python3 scripts/review_dashboard.py --paper DGJ26PracticalDynamicsRCV --precheck` before
handoff so missing/stale statement-audit rows are explicit.
If any paper-facing theorem takes a hypothesis that is not proved from prior
Lean declarations, declare that hypothesis in `Assumptions.lean`, list it in
`status.json` `review_surface.assumption_names`, and populate
`assumption_match_llm.json` with an independent judgment that it is a true
paper/source model assumption rather than a proof shortcut.
The repository audit follows paper-local helper chains recursively: a theorem
is not closed if any helper it depends on still consumes an unvalidated
certificate, source-row equation, hidden hypothesis, or proof-boundary premise.
Do not use `axiom`, `constant`, `opaque`, or unsafe declarations to bypass that
provenance boundary.
If the dashboard has more than 30 rows, also populate `review_surface_llm.json`
with a no-paper-context LLM audit that checks whether every dashboard row is a
paper-facing definition, formula, or named statement. At 120 or more rows, treat
the dashboard as oversized and curate `PaperInterface.lean` or
`status.json.review_surface.include_names` before broad human review.
Before a full-formalization closeout, rerun
`python3 scripts/review_dashboard.py --paper DGJ26PracticalDynamicsRCV --paper-coverage-precheck`
and resolve missing, stale, partial, or uncertain source coverage.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
| RCV ballots and first-active candidate membership | `paper_ballot_suffix_extension`, `paper_ballot_prefix_extension`, `paper_ballot_respects_length`, `paper_single_choice_ballot`, `paper_exhausted_prefix_at_active_set` | formalized | `PaperInterface.lean` | None |
| Proposition 1: robust extensions of Algorithm 1 | `paper_proposition1_from_algorithmA_support_count_loop_invariants_linear_runtime`, `paper_proposition1_from_algorithmA_append_suffix_then_prefix_linear_runtime` | formalized | `PaperInterface.lean` | None; the reviewed row uses the DGJ24 Algorithm A support-count route and inherited linear runtime |
| Proposition 2: exhausted-ballot completion winners | `paper_exhausted_completion_viable`, `paper_exhausted_completion_viable_candidates`, `paper_proposition2_exhausted_completion_equivalent`, `paper_proposition2_exhausted_completion_activates_candidate`, `paper_proposition2_exhausted_completion_active_support_count`, `paper_proposition2_viable_candidates_characterization`, `paper_proposition2_multi_round_closeout_from_algorithmA_count_test` | formalized | `PaperInterface.lean` | None |
| Theorem 2.1: strengthened removal after one-survival round | `paper_theorem2_1_concrete_canonical_generated_source_branch_implementation_sound_and_quartic_runtime`, `paper_theorem2_1_concrete_full_election_run_implementation_sound_and_quartic_runtime` | formalized | `PaperInterface.lean` | None |
| Theorem 2.2: multi-winner containment with early winner | `paper_algorithm4_pairwise_condition`, `paper_theorem2_2_algorithm4_pairwise_condition_sound_and_profile_quadratic_verification` | formalized | `PaperInterface.lean` | None; Algorithm 4's Eq. (2)/(3) pairwise condition is exposed as a source-facing formula row |
| Empirical election audit findings | `none` | not formalized | `none` | Data/code scope outside the Lean theorem ledger |

## Intake Checklist

- [ ] Confirm the official PDF URL, version, and bibliographic fields.
- [ ] Extract/confirm all named definitions, lemmas, and theorems in source order.
- [ ] Fill in `FORMALIZATION_PLAN.md` with the initial outside-Lean paper audit,
      formula/result sanity check, proof strategy, and likely hard seams before
      deep Lean work.
- [ ] Record the shared-library reuse checkpoint: mathlib, cslib, optlib, and
      `EconCSLib` modules/declarations inspected; API chosen; near-misses.
- [ ] Record the formal target map: rows to prove, empirical/out-of-scope rows,
      and any explicit boundary that would remain if the paper cannot close now.
- [ ] Run the lightweight statement target-setting pass and fix mismatched
      theorem targets before serious proof work.
- [ ] Run the assumption/hidden-premise precheck after the statement pass; do
      not treat row-local statement matches as globally certified targets until
      premise provenance also clears.
- [ ] Confirm `python3 scripts/audit_repository.py` reports no recursive
      paper-local hidden-premise dependency or axiom-like declaration for this
      paper.
- [ ] Populate `DependencyDAG.tex` with the same named-result inventory.
- [ ] Replace placeholders in `MainTheorems.lean` and `PaperInterface.lean`
      before updating any status row.
- [ ] Keep `PaperInterface.lean` and `status.json` `review_surface` limited to
      source-facing definitions and named statements.
- [ ] Route every non-derived paper-facing theorem premise through
      `Assumptions.lean`, then run the assumption-provenance LLM judge.
- [ ] If the dashboard has more than 30 rows, run the LLM review-surface audit;
      if it has 120 or more rows, curate the interface before broad review.
- [ ] Run the context-free Lean-to-TeX translation and third-LLM match judgment
      workflow before asking for human dashboard review.
- [ ] Update `status.json`, then run `python3 scripts/sync_paper_status.py`.
- [ ] Rebuild `DependencyDAG.pdf` and verify visually after each significant edit.

## Post-Formalization Checklist

- [ ] Run a library elevation pass over paper-local proof modules and record
      reusable candidates or completed extractions in `FINAL_VALIDATION_REPORT.md`.
- [ ] Update `DependencyDAG.tex`, rerender `DependencyDAG.pdf`, inspect the
      rendered diagram, and record the DAG audit evidence in both
      `FINAL_VALIDATION_REPORT.md` and `POST_FORMALIZATION_AUDIT.md`.
- [ ] Run the targeted repository audit after the report/DAG updates:
      `python3 scripts/audit_repository.py --paper DGJ26PracticalDynamicsRCV --paper-closeout --include-active --info-limit 0`.
      This audit includes the DAG/final-report closeout gate; resolve all
      findings for this paper before claiming the post-formalization workflow is
      complete.
- [ ] Run the combined recursive provenance audit and write a closeout report:
      `python3 scripts/audit_repository.py --include-active --library-premise-audit --info-limit 0 --write-report docs/RECURSIVE_PROVENANCE_AUDIT_<date>.md`.
      Resolve all findings for this paper before claiming `formalized`; if a
      finding remains, mark the result partial/conditional in `status.json`,
      `DependencyDAG.tex`, and `FINAL_VALIDATION_REPORT.md`.
