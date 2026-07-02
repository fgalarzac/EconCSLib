# Start Here: DGJ24

Current status: mechanically closed formalization with caveat, 65 curated
paper-facing rows.

Begin by running:

```bash
lake build EconCSLib.SocialChoice.Voting.STV
lake env lean papers/DGJ24OptimalStrategiesRCV/PaperInterface.lean
```

Read in this order:

0. `../../docs/plans/DGJ_RCV_HANDOFF_2026-07-01.md`
1. `FINAL_VALIDATION_REPORT.md`
2. `FORMALIZATION_PLAN.md`
3. `PaperInterface.lean`
4. `MainTheorems.lean`

DGJ24 now passes the mechanical post-formalization checks:

```bash
python3 skills/econcs-formalizer/scripts/source_record_audit.py --paper DGJ24OptimalStrategiesRCV --root . --out papers/DGJ24OptimalStrategiesRCV/source_record_audit.json --max-lean-output-chars 30000
python3 scripts/review_dashboard.py --paper DGJ24OptimalStrategiesRCV --statement-check
python3 scripts/review_dashboard.py --paper DGJ24OptimalStrategiesRCV --paper-coverage-check
python3 scripts/review_dashboard.py --paper DGJ24OptimalStrategiesRCV --source-to-lean-check
python3 scripts/audit_repository.py --paper DGJ24OptimalStrategiesRCV --paper-closeout --include-active --info-limit 0
```

The closeout state is:

- `source_record_audit.json`: 65 configured review rows, zero boundary inputs,
  zero recursion failures.
- `review_surface_llm.json`, `lean_to_tex_llm.json`,
  `statement_match_llm.json`, and `paper_coverage_llm.json` are current for the
  65-row review surface.
- `audit_repository.py --paper-closeout` reports zero errors and zero warnings.
- Human dashboard sign-off has not yet been recorded.

Important reviewed endpoints:

- Theorem 3.1:
`paper_theorem3_1_from_algorithm3_generated_structure_final_order_clipped_candidate_allocations_optimal_and_linear_runtime`.
- Theorem 3.2:
  `paper_theorem3_2_algorithm6_source_condition_sound_and_profile_quartic_runtime`.
- Proposition 3.4:
  `paper_proposition3_4_concrete_coverage_implementation_sound_and_profile_quadratic_runtime_from_sorted_strict_support_predict_losses_canonical_profile_constructed_generated_winners_computed_top_first_choice`.
  This replaces the older reviewed finite Predict-Wins source-winner checker
  endpoint; the checker route remains auxiliary only.
- Theorem 5.4:
  `paper_aux_final_order_round_winners_caseA_minimizer_strategy_characterization`.
- Proposition 5.6:
  `paper_proposition5_6_selfish_beneficial_other_may_disadvantage_singleton_witness`.

For DGJ26 reuse, the auxiliary bridge
`paper_algorithm3_exact_fill_support_count_data_of_loop_data` converts the
stronger source-shaped Algorithm 3 support-count loop semantics into the
proof-carrying exact-fill support-count data used by weaker downstream routes.
