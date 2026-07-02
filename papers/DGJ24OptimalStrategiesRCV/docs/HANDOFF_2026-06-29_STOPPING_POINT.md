# Handoff: 2026-06-29 DGJ24

Historical handoff. For the current continuation plan, use
`../../docs/plans/DGJ_RCV_HANDOFF_2026-07-01.md`.

Stopped at a clean partial-proof boundary.

What is done:

- `Voting.Ballot` has reusable prefix/blocker accumulator APIs for strict
  support and budgeted quota checks, plus current-prefix ready-set constructors
  for source-loop selections.
- Proposition 3.4 has a direct prefix-form route through
  `paper_predict_wins_budget_accumulator_quota_at_prefixes` and
  `paper_proposition3_4_sequence_reduction_sound_and_quadratic_runtime_from_budgeted_predict_wins_prefixes_and_predict_losses`.
- Proposition 3.4 also has
  `paper_proposition3_4_sequence_reduction_sound_and_quadratic_runtime_from_algorithm7_source_loops`,
  which consumes the concrete Algorithm 7 source-loop facts directly.
- DGJ24 now exposes `paper_predict_wins_budget_ready_candidates_at_prefix`,
  `paper_predict_wins_budget_accumulator_quota_at_prefixes_of_loop_ready_candidates`,
  `paper_predict_losses_loop_prefix`, and
  `paper_predict_losses_initial_loss_prefix_certificate_of_loop_prefix`.
- `MainTheorems.lean` has
  `sequenceBoundsCover_of_budgetReadyPredictWinsSelections_and_predictLossesLoopPrefixes`,
  which composes the Predict-Wins ready-set facts and Predict-Losses loop
  prefix facts into the bounds-coverage core.
- `MainTheorems.lean` also has
  `mem_predictWinsBudgetReadyCandidatesAtPrefix_iff` and
  `predictLossesLoopPrefix_of_sourceInequalities`, reducing the remaining
  Algorithm 7 loop obligations to the paper's strict-support inequalities.
- The shared `RoundOutcome` layer now has `initialLossCount` and
  `HasInitialLossPrefix`; DGJ24 has
  `sequenceBoundsCover_of_budgetReadyPredictWinsSelections_and_predictLossesLoopPrefixes_rcvSequence`
  and
  `proposition3_4_boundedSequenceFamily_covers_and_quadraticRuntime_of_budgetReadyPredictWinsSelections_and_predictLossesLoopPrefixes_rcvSequence`
  for concrete RCV win/loss sequences, plus
  `proposition3_4_sequenceReduction_sound_and_quadratic_runtime_of_budgetReadyPredictWinsSelections_and_predictLossesLoopPrefixes_rcvSequence`
  for the full sequence-reduction specification route.
- The shared STV trace layer now reads concrete elect/eliminate trace steps into
  a win/loss sequence via `STVTrace.roundOutcomeSequence`, and proves that a
  `STVTrace.HasInitialEliminationPrefix` yields the corresponding
  `RoundOutcome.HasInitialLossPrefix`.
- The shared STV trace layer also has
  `STVTrace.HasInitialEliminationFocusPrefix`, which records the concrete
  eliminated candidates in the initial prefix and derives
  `STVTrace.HasInitialEliminationPrefix`.
- DGJ24 now exposes `rcvSequenceFromTrace`,
  `rcvSequenceHasInitialLossPrefix_of_trace_initialEliminationPrefix`,
  `rcvSequenceHasInitialLossPrefix_of_trace_initialEliminationFocusPrefix`,
  `sequenceBoundsCover_of_budgetReadyPredictWinsSelections_and_predictLossesLoopPrefixes_rcvTrace`,
  and
  `proposition3_4_sequenceReduction_sound_and_quadratic_runtime_of_budgetReadyPredictWinsSelections_and_predictLossesLoopPrefixes_rcvTrace`.
- `PaperInterface.lean` now also exposes the focused-trace paper route
  `paper_proposition3_4_sequence_reduction_sound_and_quadratic_runtime_from_algorithm7_trace_source_loops`.
- The current curated interface is 71 paper-facing rows in `status.json`.
- README, formalization plan, DAG, and stopping validation report are updated.

What is not done:

- The concrete Predict-Wins traversal still needs selected-at-prefix
  ready-set membership facts.
- The concrete Predict-Losses traversal still needs the semantic proof that
  Algorithm 7's transfer/threshold loop yields
  `trace.HasInitialEliminationFocusPrefix (lossPrefix problem sequence)` for
  the concrete source trace associated with each feasible sequence.
- Theorem 3.2, Theorem 3.1, Section 5, and Appendix B.2 still have visible
  source-constructor boundaries.

Next proof target:

Construct the Algorithm 7 source-loop proof that instantiates the Predict-Wins
ready-set membership facts and derives the concrete focused trace
initial-elimination prefix from the Predict-Losses transfer/threshold loop,
then feed the focused RCVTrace Proposition 3.4 theorem.

Validation target:

```bash
lake build EconCSLib.SocialChoice.Voting.STV
lake env lean papers/DGJ24OptimalStrategiesRCV/PaperInterface.lean
```
