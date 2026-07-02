# Formalization Notes

This file preserves the previous hand-written paper-folder README content.
The GitHub-facing `README.md` is now a generated status overview.

# Optimal Strategies in Ranked-Choice Voting

## Source Version

- Paper: *Optimal Strategies in Ranked-Choice Voting*
- Authors: Sanyukta Deshpande; Nikhil Garg; Sheldon H. Jacobson
- Version formalized: arXiv:2407.13661; working paper
- Official URL: https://arxiv.org/abs/2407.13661
- Public PDF: https://arxiv.org/pdf/2407.13661.pdf

The PDF is cached locally as `source.pdf` and ignored by Git. The extracted text
cache is `source.txt` when `pdftotext` succeeds, and is also ignored by Git in
public workspaces unless redistribution rights have been checked separately.

## Paper-Facing Ledger

- Implementation theorem file: `DGJ24OptimalStrategiesRCV/MainTheorems.lean`
- Human-facing theorem file: `DGJ24OptimalStrategiesRCV/PaperInterface.lean`
- Machine-readable status source: `DGJ24OptimalStrategiesRCV/status.json`
- Outside-Lean proof plan: `DGJ24OptimalStrategiesRCV/docs/FORMALIZATION_PLAN.md`
- Final validation report: `DGJ24OptimalStrategiesRCV/FINAL_VALIDATION_REPORT.md`
- Next-agent starting point: `DGJ24OptimalStrategiesRCV/docs/START_HERE_NEXT_AGENT.md`
- Stopping-point handoff: `DGJ24OptimalStrategiesRCV/HANDOFF_2026-06-29_STOPPING_POINT.md`
- Dependency DAG: `DGJ24OptimalStrategiesRCV/docs/DependencyDAG.tex`
- Rendered DAG: `DGJ24OptimalStrategiesRCV/docs/DependencyDAG.pdf`

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
`python3 scripts/review_dashboard.py --paper DGJ24OptimalStrategiesRCV --statement-precheck`.
Also populate `paper_statement_map.json` for the paper's source definitions,
formulas, and named claims, then run the paper-level coverage pass and save
`paper_coverage_llm.json`: this asks whether every source statement that should
be represented is covered by at least one dashboard row. This source-to-row
accounting is separate from the row-local statement judge.
Then run `python3 scripts/review_dashboard.py --paper DGJ24OptimalStrategiesRCV
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
`python3 scripts/review_dashboard.py --paper DGJ24OptimalStrategiesRCV --precheck` before
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
`python3 scripts/review_dashboard.py --paper DGJ24OptimalStrategiesRCV --paper-coverage-precheck`
and resolve missing, stale, partial, or uncertain source coverage.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
| STV/RCV ballots, traces, structures, and constraints | `paper_rcv_structure`, `paper_structure_constraints` | formalized | `PaperInterface.lean` | None |
| Proposition 2.1: structures partition ballot space under tie-breaking | `paper_proposition2_1_unique_structure`, `paper_proposition2_1_fstv_or_constraints_same_order` | formalized | `PaperInterface.lean` | None |
| Theorem B.1: `F_STV` is a well-defined STV social welfare function | `paper_theoremB1_fstv_well_defined_order`, `paper_theoremB1_fstv_result_realized_by_constraints` | formalized | `PaperInterface.lean` | None |
| Lemma B.2: round winners and election winners relation | `paper_lemmaB2_round_winning_never_election_loser` | formalized | `PaperInterface.lean` | None |
| Proposition 3.3: feasible sequence count | `paper_proposition3_3_sequence_win_count_bound`, `paper_proposition3_3_feasible_sequence_count_bound` | formalized | `PaperInterface.lean` | None |
| Theorem 3.1: fixed-structure SmartAllocation is polynomial-time optimal | `paper_theorem3_1_from_algorithm3_generated_structure_final_order_clipped_candidate_allocations_optimal_and_linear_runtime` | formalized | `PaperInterface.lean` | None |
| Theorem 3.2: irrelevant-candidate reduction | `paper_theorem3_2_algorithm6_source_condition_sound_and_profile_quartic_runtime` | formalized | `PaperInterface.lean` | None |
| Proposition 3.4: sequence-space reduction | `paper_proposition3_4_concrete_coverage_implementation_sound_and_profile_quadratic_runtime_from_sorted_strict_support_predict_losses_canonical_profile_constructed_generated_winners_computed_top_first_choice` | formalized | `PaperInterface.lean` | None; two Algorithm 7 helper formulas are source-parameter coverage rows rather than standalone theorem gaps |
| Definition 5.1: benefit via action | `paper_benefits_via_action`, `paper_coalition_all_benefit` | formalized | `PaperInterface.lean` | None |
| Proposition 5.3: strategic voting no-all-benefit | `paper_proposition5_3_individual_no_benefit`, `paper_proposition5_3_coalition_not_all_benefit` | formalized | `PaperInterface.lean` | None |
| Theorem 5.4: optimal vote-addition strategy shapes | `paper_theorem5_4_allowed_shape`, `paper_aux_final_order_round_winners_caseA_minimizer_strategy_characterization` | formalized | `PaperInterface.lean` | None |
| Proposition 5.5: uncertainty and coalition benefit | `paper_proposition5_5_uncertainty_coalition_benefit` | formalized | `PaperInterface.lean` | None |
| Proposition 5.6: selfish robustness and non-selfish downside | `paper_eliminated_early_by_margin_less_than_added_votes`, `paper_proposition5_6_selfish_beneficial_other_may_disadvantage_singleton_witness` | formalized | `PaperInterface.lean` | None |

Latest closeout checkpoint: `lake build EconCSLib.SocialChoice.Voting.STV`
followed by
`lake env lean papers/DGJ24OptimalStrategiesRCV/PaperInterface.lean` passes
for the curated 65-row review surface. The recursive source-record audit
reports zero boundary inputs and zero recursion failures, and
`python3 scripts/audit_repository.py --paper DGJ24OptimalStrategiesRCV --paper-closeout --include-active --info-limit 0`
reports zero errors and zero warnings. Human dashboard review is still `0/65`.

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
- [x] Replace placeholders in `MainTheorems.lean` and `PaperInterface.lean`
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
      `python3 scripts/audit_repository.py --paper DGJ24OptimalStrategiesRCV --paper-closeout --include-active --info-limit 0`.
      This audit includes the DAG/final-report closeout gate; resolve all
      findings for this paper before claiming the post-formalization workflow is
      complete.
- [ ] Run the combined recursive provenance audit and write a closeout report:
      `python3 scripts/audit_repository.py --include-active --library-premise-audit --info-limit 0 --write-report docs/RECURSIVE_PROVENANCE_AUDIT_<date>.md`.
      Resolve all findings for this paper before claiming `formalized`; if a
      finding remains, mark the result partial/conditional in `status.json`,
      `DependencyDAG.tex`, and `FINAL_VALIDATION_REPORT.md`.
