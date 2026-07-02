# Formalization Plan: Optimal Strategies in Ranked-Choice Voting

This is a working scratchpad for outside-Lean proof thinking. Keep it short and
useful; it is not the final validation report.

- Namespace: `DGJ24OptimalStrategiesRCV`

## Initial Outside-Lean Paper Audit

- Source version / local files inspected: arXiv:2407.13661v2, local
  `source.pdf`, and local `source.txt`.
- Source/version mismatch notes: none identified yet. The website title uses
  "Ranked-Choice"; the PDF title line uses "Ranked Choice".
- Complete named-result ledger status: first-pass source-text inventory
  completed from `source.txt`; TeX/source archive is not cached yet.
- Formula sanity check:
  - Signs, constants, normalizations, quantifiers, domains: not fully checked.
    The first formulas needing careful treatment are Droop quota `Q`,
    structure-count `2^(n-1)`, feasible-sequence bound `sum_{j=1}^k binom n j`,
    strict-support definitions, and the nonlinear transfer constraints in
    Appendix B.2.
  - Density vs mass / likelihood-kernel representation issues: not applicable;
    finite ballot counts and fractional transfers are the core objects.
  - Dependency map between named source results: Proposition 2.1 and Theorem
    B.1 define the STV structure/replay layer; Lemma B.2 feeds Proposition
    3.3; Lemma C.1 feeds Theorem 3.2; Theorem 3.1 feeds later strategy
    statements; Theorems 5.4 and Propositions 5.3/5.5/5.6 are downstream
    strategy results.
  - Formula-bearing displayed claims that need derivation, not source-row
    assumptions: Appendix B.2 constraints, strict-support formulas in Appendix
    C, and slack/allocation inequalities in Theorem 3.1.
- Named result sanity check:
  - Results that look correct as stated: no contradiction found in the initial
    scan. The finite STV structure/replay layer is a plausible first Lean
    target.
  - Suspected bugs, missing assumptions, or ambiguous wording: tie-breaking is
    essential in Proposition 2.1; runtime/algorithmic complexity claims should
    be explicit certificate boundaries until the algorithm model is encoded.
- Shared-library reuse checkpoint:
  - Mathlib declarations/modules inspected: `Finset`, `List`, finite types, and
    natural-number arithmetic through the new voting skeleton.
  - Cslib declarations/modules inspected: none yet.
  - Optlib declarations/modules inspected: none present in this checkout.
  - Existing `EconCSLib` declarations/modules inspected:
    `EconCSLib.SocialChoice.Ranking.Basic` and the new
    `EconCSLib.SocialChoice.Voting` modules.
  - API chosen and near-misses: start with partial-list ballots and deterministic
    trace structures under `EconCSLib.SocialChoice.Voting`; do not overload the
    existing `Ranking` permutation API because STV uses partial ballots,
    exhaustion, transfers, and active-candidate filtering.
- Proof strategy consequences:
  - Source proof route to follow: first formalize deterministic STV structure
    validity/replay and final order/sequence vocabulary, then fixed-structure
    smart-allocation certificates.
  - Cleaner Lean route or reusable library route: use shared `Voting.Ballot`,
    `Voting.STV`, and `Voting.STV.Structures` as the paper-neutral layer; keep
    structure-specific nonlinear constraints paper-local until a second paper
    actually needs them.
  - Major issues already reported to the user: roadmap author metadata was
    stale and has been corrected.

## Source Inventory

- Definitions / formatted paper objects:
  - STV/RCV mechanism, Droop quota, active candidates, vote tally/paths,
    order/sequence structure, structure-specific constraints, strategic
    additions, strict support, benefit via action, and Assumption 5.2.
- Named lemmas / propositions / theorems / corollaries:
  - Example 2.1, Proposition 2.1, Theorem 3.1, Theorem 3.2, Proposition 3.3,
    Proposition 3.4, Definition 5.1, Assumption 5.2, Proposition 5.3, Theorem
    5.4, Proposition 5.5, Proposition 5.6, Examples A.1/A.2, Theorem B.1,
    Lemma B.2, Lemma C.1, and Algorithms 1--7.
- Theorem-like displayed claims that are used later:
  - Appendix B.2 nonlinear constraints for a fixed structure, Appendix C
    strict-support formulae, and allocation-rule slack inequalities.

## Initial Proof Strategy

- Main theorem chain: Proposition 2.1 / Theorem B.1 -> Lemma B.2 ->
  Proposition 3.3 -> Theorem 3.1 -> Theorem 3.2 / Proposition 3.4 ->
  Section 5 strategy results.
- Likely reusable `EconCSLib` seams: ballot exhaustion, next-active preference,
  active-set shrinking, deterministic trace replay, structure validity,
  prefix/suffix robustness, and vote-addition certificates.
- Paper steps that look underspecified or analytically hard: polynomial runtime
  claims, SmartAllocation optimality, irrelevant-candidate removal proofs, and
  all empirical case-study claims.
- Formal target map:
  - Rows to fully prove now: generic ballot/trace invariants and the first
    fixed-structure replay boundary for Proposition 2.1 / Theorem B.1.
  - Empirical/descriptive rows out of formal theorem scope: Republican-primary
    case study, bootstrap results, runtime claims from implementations, and
    example tables unless separately encoded.
  - Explicit assumption/certificate boundaries, if any: deterministic
    tie-breaking, source-specific STV transfer rule, SmartAllocation runtime
    certificate, and data/code boundaries.
- Planned fallback route if the source proof is too informal: expose
  source-shaped certificate structures for structure replay and allocation
  optimality, then mark downstream theorem rows partial until the constructors
  are derived.

## Reusable-Library TODO

- Library APIs to use directly:
  `EconCSLib.SocialChoice.Voting.OrderSequenceStructure`,
  `StructureConstraints`, `StructureConstraintCharacterization`,
  `StructurePartition`, `StructureOutcomeAgreement`, and the existing
  `STVTrace`/`StructureReplay` skeleton plus `ActiveUntilExitRank`.
- Small reusable lemmas to add now:
  structure-partition existence/uniqueness projections, classifier-to-partition
  and classifier-to-agreement bridges, fixed-length sequence win-position
  counting, the active-until-exit-rank bridge, and the direct
  `StructureOutcomeAgreement` bridge are now in
  `EconCSLib.SocialChoice.Voting.STV`/`STV.Structures`; generic
  minimizer/maximizer/soundness certificates, including the shared
  `AlgorithmSoundnessCertificate.of_condition` condition-to-spec lift used by
  the Algorithm 6 and Algorithm 7 certificates, live in
  `EconCSLib.Foundations.Optimization.Certificate`.  The strict-support
  group-removal condition, separated safety predicate, minimum-tally
  elimination, focused-candidate removal, active-group-cardinality decrease,
  and quota-block counting lemmas now live in shared library APIs rather than
  DGJ24-only predicate bodies.
- Larger reusable components to defer:
  Appendix B.2 constraint generation from concrete STV transfer semantics,
  SmartAllocation lower-bound certificate constructors, irrelevant-candidate
  removal constructors, and the Section 5 behavioral/witness derivations.
- Library-audit risks:
  the shared structure, sequence-counting, and optimization-certificate APIs are
  paper-neutral, but the current DGJ24 paper rows still expose source-facing
  classifier/certificate boundaries for generated constraints, algorithm
  constructors, and Section 5 strategy witnesses.

## Execution Checklist

- [ ] Download/cache source PDFs and text extracts, with redistribution notes.
- [x] Complete named-result and formula-bearing displayed-claim inventory for
      the current partial review surface.
- [x] Fill the formal target map and declare the current boundary/certificate
      rows.
- [x] Build or select reusable library APIs before adding paper-local wrappers.
- [x] Replace paper scaffold with source-facing Lean definitions and rows.
- [ ] Prove all rows marked in-scope, or keep them partial with an explicit
      boundary note.
- [x] Update README and status from the current 71-row review surface.
- [ ] Update DAG and final validation report only at a closeout or handoff
      boundary.
- [x] Run targeted build and row/coverage/assumption audit checks for the
      current review surface.
- [ ] Record any unresolved source bug, assumption, or library debt.

## Active Scratchpad

- Current Lean endpoint:
  `paper_proposition2_1_unique_structure`,
  `paper_proposition2_1_fstv_or_constraints_same_order`,
  `paper_theoremB1_fstv_well_defined_order`,
  `paper_theoremB1_fstv_result_realized_by_constraints`,
  `paper_lemmaB2_round_winning_never_election_loser`,
  `paper_proposition3_3_sequence_win_count_bound`,
  `paper_proposition3_3_feasible_sequence_count_bound`,
  the Theorem 3.1/3.2 and Proposition 3.4 certificate projections, the
  SmartAllocation slack-to-lower-bound constructor
  `smartAllocationLowerBoundCertificate_of_slackCertificate`, the componentwise
  Algorithm 3 slack-filling core
  `paper_theorem3_1_slack_filling_core_optimal_and_linear_runtime`, the
  source-shaped STV-to-slack reduction bridge
  `paper_theorem3_1_from_slack_reduction_optimal_and_linear_runtime`, the Lemma
  C.1 ballot-reduction active-support bridge
  `paper_lemmaC1_removed_candidates_active_support_preserved`, Definition C.2
  `paper_strict_support_count`, Algorithm 6's
  `paper_candidate_group_removal_condition`, the separated safety theorem
  `paper_algorithm6_group_condition_implies_safety`, the exact-runtime
  constructor `irrelevantCandidateRemovalConditionCertificate_of_exactRuntime`,
  the Algorithm 6 trace-elimination certificate
  `paper_theorem3_2_from_trace_certificate`,
  and the
  Proposition 3.4 exact-runtime constructor
  `sequenceReductionSoundnessCertificate_of_exactRuntime`, Algorithm 7
  Predict-Wins/Predict-Losses filters
  `paper_predict_wins_candidates` / `paper_predict_losses_candidates`, the
  ordered Predict-Wins support accumulator `paper_predict_wins_support`, the
  quota-capacity upper-win arithmetic theorem
  `paper_proposition3_4_bounds_cover_from_prediction_capacity`, the
  quota-block coverage theorem
  `paper_proposition3_4_bounds_cover_from_quota_blocks`, the
  source-shaped capacity/loss-floor certificate
  `paper_proposition3_4_from_prediction_capacity_certificate`, the
  quota-block counting certificate
  `paper_proposition3_4_from_quota_block_certificate`, the
  prefix-form budgeted Predict-Wins condition
  `paper_predict_wins_budget_accumulator_quota_at_prefixes`, the
  current-prefix Predict-Wins ready-set constructor
  `paper_predict_wins_budget_accumulator_quota_at_prefixes_of_loop_ready_candidates`,
  the Predict-Losses ordered-loop-prefix constructor
  `paper_predict_losses_initial_loss_prefix_certificate_of_loop_prefix`, the
  direct Algorithm 7 source-loop route
  `paper_proposition3_4_sequence_reduction_sound_and_quadratic_runtime_from_algorithm7_source_loops`,
  the shared trace-to-win/loss-sequence bridge and DGJ24 RCVTrace route for
  Algorithm 7 initial-loss semantics,
  the
  direct prefix-form Algorithm 7 route
  `paper_proposition3_4_sequence_reduction_sound_and_quadratic_runtime_from_budgeted_predict_wins_prefixes_and_predict_losses`,
  the
  sequence-bound coverage predicate `paper_sequence_bounds_cover`, the bounded
  family coverage theorem
  `paper_proposition3_4_bounded_sequence_family_covers`, and the Section 5
  benefit/strategy/uncertainty/robustness interfaces build under
  `lake build EconCSLib.SocialChoice.Voting.STV` followed by
  `lake env lean papers/DGJ24OptimalStrategiesRCV/PaperInterface.lean`.
  Proposition 5.3 and the ex-post
  side of Proposition 5.5 now derive the first-exiting coalition member from
  finite exit ranks, round ranks, and the reusable active-until-exit-rank
  invariant rather than assuming a packaged witness.
- Exact current mathematical gap:
  discharge the visible source-facing boundaries now exposed in
  `PaperInterface.lean`: the Appendix B.2 deterministic structure classifier
  whose generated constraints characterize the unique structure and whose final
  order agrees with direct STV, the concrete SmartAllocation reduction
  certificate from target-structure dynamics that feeds the checked
  STV-to-slack bridge and lower-bound optimality/runtime certificate,
  the remaining irrelevant-candidate-removal preservation constructor that
  proves the concrete reduced-instance output specification from the
  Algorithm 6 group-elimination trace fact, with condition-to-safety,
  minimum-tally trace elimination, and exact quartic runtime constructors
  already packaged,
  concrete Predict-Wins ready-set membership facts and the proof that the
  Predict-Losses transfer/threshold loop yields the trace
  initial-elimination prefix consumed by the RCVTrace Algorithm 7 route.
  Quota-block and support-sum routes remain available as alternate
  sufficient certificate paths, and exact quadratic runtime is already packaged,
  the fully encoded strategic-voting dynamics that instantiate finite exit
  ranks, round ranks, and active-until-exit-rank invariants, the Appendix E
  split-replacement certificate constructor, the Case-(A) post-win-surplus
  certificate constructor, and the Proposition 5.5 ex-ante witness.
- Next bridge lemmas to try:
  attack Proposition 3.4's source-loop constructor next: prove each concrete
  Predict-Wins traversal selection belongs to
  `paper_predict_wins_budget_ready_candidates_at_prefix`, then use
  `paper_predict_wins_budget_accumulator_quota_at_prefixes_of_loop_ready_candidates`;
  prove the concrete Predict-Losses transfer/threshold loop yields
  `trace.HasInitialEliminationPrefix (lossPrefix sequence).length`, then use
  `rcvSequenceHasInitialLossPrefix_of_trace_initialEliminationPrefix` and the
  RCVTrace Algorithm 7 routes.
  The implementation theorem
  `sequenceBoundsCover_of_budgetReadyPredictWinsSelections_and_predictLossesLoopPrefixes`
  composes those facts into the bounds-coverage core, which then feeds
  `paper_proposition3_4_sequence_reduction_sound_and_quadratic_runtime_from_algorithm7_source_loops`
  without exposing the recursive accumulator certificate. If this stalls,
  continue the Theorem 3.2 route: use the shared strict-support voter/count API
  and the Algorithm 6 `candidateGroupRemovalCondition` to build the
  preservation bridge from the group-elimination trace fact to the concrete
  output specification, with exact quartic runtime already packaged.
- Informal proof sketch / recurrence / construction:
  recurse over the active candidate set. At each round, deterministic
  tie-breaking chooses either the highest candidate over quota or the lowest
  tally candidate; append `W` or `L`, remove that candidate from the active
  set, and transfer votes according to the paper's deterministic transfer
  convention. The constraint partition follows once each branch condition is
  mutually exclusive and exhaustive under tie-breaking.

## Source Notes And Assumptions

- Source imprecision or source-note item to report later:
- Genuine paper assumptions to declare in `Assumptions.lean`:
  none currently. Deterministic tie-breaking, Appendix B.2 constraint
  classifier construction, algorithm certificates, and Section 5 behavioral
  witnesses are explicit partial proof boundaries rather than source-assumption
  declarations.
- Temporary certificate fields to discharge:
  the Appendix B.2 classifier characterization and direct-run agreement,
  `paper_smart_allocation_certificate`,
  `paper_irrelevant_candidate_removal_certificate`,
  `paper_sequence_reduction_certificate`,
  `paper_other_shape_strict_cost_dominance`, and the Section 5 premises listed
  in `statement_match_llm.json` as conditional boundaries.  For Proposition
  5.3/5.5, the remaining visible Section 5 premises are now finite exit ranks,
  round ranks, active-until-exit-rank dynamics, coalition prefix preservation,
  and the Proposition 5.5 ex-ante witness rather than an opaque
  first-exiting-member witness.
- Validation/audit checks that must inspect these assumptions:
  statement and paper-coverage sidecars classify the current certificate and
  Section 5 rows as conditional boundaries; assumption provenance remains empty
  until a true source assumption declaration is introduced.
