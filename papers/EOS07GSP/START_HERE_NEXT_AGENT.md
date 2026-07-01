# EOS07GSP Startup Handoff

Date: 2026-07-01

This is the first file to read after the pause. It is intentionally shorter
than the older handoff and points to exact files/declarations for maintenance,
review, or optional extension work.

For the current proof strategy, read the "Fastest paper-DAG screening path"
section below before opening the large theorem files. The static Lemma 5--6
ranked-GSP mechanism bridges have now been implemented for the modeled
finite ranked mechanisms; Remark 2 uses a concrete finite position-VCG
mechanism rather than a paper-facing certificate; the strict Theorem 7
tie-broken ranked-GSP comparison endpoint derives sorted comparison slots
and no-positive transfers; and Theorem 8 is closed through the source
theorem's ex-post payoff-game/source-event route.

## Current Validation Boundary

The latest Lean validation after the concrete finite VCG endpoint and finite
strict-values source-event Theorem 8 endpoints was:

```bash
lake build EOS07GSP.ProofInterface EOS07GSP.PostPaperAudit EOS07GSP.PaperInterface EOS07GSP
```

That command passed after the latest Remark 2 finite position-VCG work,
Lemma 5--6 ranked-GSP work, Theorem 7 strict tie-broken ranked-GSP comparison
work, and the Theorem 8 ex-post payoff-game bridge. Rerun it before any
further Lean commit.

## Shared Worktree Rules

- Do not use `git reset` in this repository. Other agents may have staged or
  unstaged work.
- Do not run broad `git add .`.
- Before editing, check only the owned paths:

```bash
git status --short --branch -- \
  EconCSLib/MechanismDesign/Auctions/MainTheorems.lean \
  papers/EOS07GSP \
  skills/econcs-formalizer
```

- If committing EOS work, use `git commit --only` with explicit path names.

## Fastest Paper-DAG Screening Path

The DAG path is:

```text
Definition 4 -> Lemma 5 -> Lemma 6 -> Theorem 7 -> Theorem 8
```

The finite exact-record Theorem 8 endpoint is a closed finite/direct-PBE route
inside Theorem 8's dynamic machinery. The strongest compact Theorem 8 source
surface is now the strict ranked-values ex-post payoff-game route:
`theorem8_strict_values_named_strategy_ex_post_local_deviation` exposes the
ex-post/local-deviation component from strict source values,
`theorem8_dropout_formula_eq_bstar_threshold` identifies the paper's displayed
generalized-English dropout formula with the finite `B*` threshold, and
`theorem8_source_event_strict_values_unique_pbe_formula_conclusion` constructs
a price-sorted finite source-event unique PBE with VCG outcome, ordered payoff
package, and payments stated in the paper's dropout-price notation. The
continuous-strategy bridge now also exposes
`theorem8_continuous_generalized_english_payoff_game_strict_values_main_conclusion`,
which bundles the named continuous payoff-PBE, support uniqueness on the
nonnegative source support, and the finite source-event VCG outcome for every
payoff-PBE strategy. This is the top-down source-facing endpoint to inspect
first for Theorem 8. It uses the source theorem's ex-post content: after
history and realized values are fixed, PBE is represented by the paper's
drop/continue payoff optimality condition plus continuity.
The continuous-strategy bridge also exposes
`theorem8_continuous_source_dropout_eq_formula_at_endpoint_of_right_eq`, formalizing
the source proof's final right-continuity step at the lower endpoint, and
`theorem8_source_event_strict_values_continuous_profile_unique_source_extensive_pbe`,
showing that any continuous dropout-price strategy whose induced finite action
rule is a source-event PBE agrees with the EOS continuous formula on that finite
source profile. The
`theorem8_q_*_review` rows expose the Step 1/Step 2 payoff comparisons and
continuity/monotonicity/unboundedness facts around `q`.
The static
Lemma 5--6 path and the strict Theorem 7 tie-broken ranked-GSP comparison
endpoint are now the preferred upstream static facts to reuse before returning
to any alternate Theorem 8 source-game proof:

1. Integrate the now-closed static GSP bridges. Lean proves the Lemma 5
   one-extra ranked-GSP route: LEF supplies adjacent upward inequalities, Nash
   plus concrete adjacent undercut reports supplies adjacent downward
   inequalities, and the appendix telescoping yields stable assignment. Lean
   also proves the Lemma 6 deterministic tie-broken ranked-GSP route: strict
   constructed bids realize the next-price outcome, every unilateral report has
   the source rematch slot/payment shape, and stability gives a locally
   envy-free equilibrium. Keep the deterministic tie-breaking convention
   visible in audit prose because the source text discusses random tie-breaking
   while the constructed strict profiles have no equilibrium ties.
2. Reuse Theorem 7 through
   `paper_theorem7_ordered_ranked_canonical_tail_strict_tiebreak_gsp_comparison_paper_conclusion`
   when the comparison profile is a strict source-ordered, locally envy-free,
   tie-broken ranked-GSP profile with nonnegative bids. This theorem derives
   sorted slots, feasibility, individual rationality from Nash via a strictly
   low bid deviation under nonnegative values/clicks, and no-positive
   transfers.
3. Return to an alternate explicit Theorem 8 model only if the task is to build
   an explicit
   type-distribution/posterior semantics rather than the current ex-post
   payoff-game semantics. Local algebra, finite schedules, source event traces,
   finite-profile continuous-strategy bridges, and the payoff-game main
   conclusion are already exposed.

This is the quickest path for auditing the already formalized source rows. More
finite Theorem 8 schedule wrappers should wait unless a reviewer asks for a
different finite presentation.

## Optional Extensions

For the ex-post payoff-game reading of Theorem 8, the paper-facing proof path is
closed in Lean through
`theorem8_continuous_generalized_english_payoff_game_strict_values_main_conclusion`.
If a reviewer requires a separate fully concrete generalized-English PBE
semantics with measure-theoretic type distributions and posterior beliefs,
that is a distinct modeling project, not a current paper-facing proof gap. It
is not payment algebra, finite schedule plumbing, or another display wrapper.
The optional extension seam is:

1. a source-level continuous type/value distribution and support model;
2. concrete belief consistency/posterior semantics over generalized-English
   histories;
3. the game-level bridge from that explicit posterior-PBE definition to the
   ex-post payoff-game condition already formalized;
4. source-history generation strong enough to produce exact finite `B*`
   terminal records without assuming a schedule, no-overshoot history, or
   clock-disciplined history as input.

The formal counterexample
`paper_theorem8_bstar_ranked_threshold_ordinary_strategy_history_allows_overshoot_record`
shows that ordinary `StrategyHistory` is too weak: a rank can drop after its
finite `B*` threshold and therefore record the wrong terminal price.

The finite exact-record source-event version is closed for the ranked finite
source model. Use
`theorem8_continuous_generalized_english_payoff_game_strict_values_main_conclusion`
for the top-level ex-post payoff-game route,
`theorem8_source_event_strict_values_unique_pbe_formula_conclusion` for the
source-facing strict-values route in paper dropout-price notation,
`theorem8_source_event_strict_values_continuous_profile_unique_source_extensive_pbe`
for the continuous-strategy finite-profile uniqueness statement,
`theorem8_price_sorted_finite_schedule_source_event_strict_values_conclusion`
for the same route in threshold notation, or the older
`theorem8_price_sorted_finite_schedule_pbe_displayed_ordered_conclusion` and
`theorem8_price_sorted_finite_schedule_belief_pbe_displayed_ordered_conclusion`
when auditing the PBE-generated history boundary directly.

## What To Reuse

Use these as the strongest public entry points before adding new code:

- `theorem8_no_overshoot_strategy_history_to_exact_drop_history`
- `theorem8RealizedNewDropoutNoOvershootStatement`
- `theorem8_strategy_step_new_dropout_record_eq_threshold_of_no_overshoot`
- `theorem8_strategy_history_to_no_overshoot_strategy_history_of_realized_new_dropout_no_overshoot`
- `theorem8_strategy_history_to_no_overshoot_strategy_history_of_realized_new_dropout_no_overshoot_statement`
- `theorem8_no_overshoot_terminal_certificate_of_strategy_history`
- `theorem8_no_overshoot_terminal_certificate_of_strategy_history_realized_new_dropout`
- `theorem8_no_overshoot_terminal_certificate_of_strategy_history_realized_new_dropout_statement`
- `theorem8_strategy_history_realized_new_dropout_source_extensive_trace_all_terminal_vcg_conclusion`
- `theorem8_strategy_history_realized_new_dropout_statement_source_extensive_trace_all_terminal_vcg_conclusion`
- `theorem8_clock_disciplined_strategy_history_to_exact_drop_history`
- `theorem8_clock_disciplined_strategy_history_final_record_eq_threshold`
- `theorem8_cold_start_clock_disciplined_strategy_history_final_record_eq_threshold`
- `theorem8_no_overshoot_strategy_history_belief_source_extensive_trace_all_terminal_vcg_conclusion`
- `theorem8_cold_start_clock_disciplined_terminal_history_belief_source_extensive_trace_completed_threshold_conclusion`
- `theorem8_cold_start_clock_disciplined_terminal_history_belief_source_extensive_trace_all_terminal_vcg_conclusion`
- `theorem8_strict_ordered_fin_schedule_belief_source_extensive_displayed_rank_formulas_of_threshold_sorted`
- `theorem8_complete_finite_schedule_pbe_displayed_ordered_conclusion`
- `theorem8_complete_finite_schedule_belief_pbe_displayed_ordered_conclusion`
- `theorem8_price_sorted_finite_schedule_pbe_displayed_ordered_conclusion`
- `theorem8_price_sorted_finite_schedule_belief_pbe_displayed_ordered_conclusion`
- `theorem8_ex_post_local_deviation_exact_history_source_full_conclusion_terminal_record_outcome_eq_bstar`

Search for them with:

```bash
rg -n "theorem8_no_overshoot_strategy_history_to_exact_drop_history|theorem8_clock_disciplined_strategy_history_to_exact_drop_history|price_sorted_finite_schedule_pbe_displayed_ordered|belief_source_extensive_trace_all_terminal|ex_post_local_deviation_exact_history_source_full_conclusion" papers/EOS07GSP EconCSLib/MechanismDesign/Auctions
```

## Optional Extension Target

If building the alternate full posterior-PBE Theorem 8 source model, do this
in this order:

1. Do not add another final-conclusion wrapper. The next real semantic target
   would be a concrete posterior/belief PBE definition and a theorem that it
   implies the ex-post payoff-game PBE condition used by
   `Theorem8ContinuousGeneralizedEnglishPayoffGame.PerfectBayesianEquilibrium`.
   The payoff-game stack already turns that condition into formula uniqueness
   and VCG outcome.
2. If the concrete source game is represented through histories first, prove
   the game-level `isSequentiallyRational` iff
   `paper_theorem8_bstar_ranked_threshold_source_sequential_rationality_statement`,
   then reuse
   `paper_theorem8_bstar_ranked_threshold_source_sequential_rationality_iff_local_deviation`.
   This should be a semantics theorem, not a certificate field.
3. After the local-deviation bridge is proved, prove the source-history
   invariant needed for exact records. The useful one-step statement should
   supply the no-overshoot premise consumed by
   `theorem8_strategy_history_to_no_overshoot_strategy_history_of_realized_new_dropout_no_overshoot`
   and its one-step record form
   `theorem8_strategy_step_new_dropout_record_eq_threshold_of_no_overshoot`,
   or else prove the named source-timing premise
   `theorem8RealizedNewDropoutNoOvershootStatement`.
4. Lift the one-transition invariant to histories, then feed the resulting
   history into the existing cold-start clock-disciplined or no-overshoot
   source-extensive endpoints.
5. Only after that, update `PaperInterface.lean` and `PostPaperAudit.lean` with
   a small paper-facing theorem. If no explicit posterior semantics is required,
   do not reopen the current formalized source inventory.

If a future alternate posterior-PBE semantics permits overshoot, do not hide
that with a wrapper. Either formalize the modeling assumption that rules it
out, switch to a finite-bidder source model whose transition rule prevents
overshoot, or record that alternate theorem as conditional on
no-overshoot/clock-discipline.

## What Not To Spend Time On

- Do not add more finite-schedule endpoints unless a reviewer asks for a
  different finite presentation or the endpoint removes a source-history
  premise from the full theorem. The canonical finite direct-PBE endpoint is
  already exposed.
- Do not try to derive an all-ranks-inactive conclusion from a finite schedule
  in the current `ℕ`-rank cold-start model. Lean already proves
  `theorem8_cold_start_clock_sorted_finite_schedule_leaves_active_unscheduled_rank`.
- Do not replace source-facing proof work with a reduced-form dynamic-game
  certificate. Reduced-form endpoints validate certificate plumbing; they are
  not substitutes for the current ex-post payoff-game/source-event route.

## Files To Read

Read in this order:

1. `README.md`, especially the handoff and Theorem 8 source-audit sections.
2. `THEOREM8_SOURCE_PROOF_PLAN.md` only as a historical proof-route ledger, not
   as the current status source.
3. `POST_PAPER_AUDIT_REPORT.md`, especially the Theorem 8 history-semantics,
   source-extensive, and belief-explicit audit bullets.
4. `FINAL_VALIDATION_REPORT.md` for the paper-facing source inventory and
   validation status.
5. `HANDOFF_2026-05-06.md` only if you need the older detailed declaration
   ledger.

## Validation Commands

After any Lean edit:

```bash
lake build EOS07GSP.ProofInterface EOS07GSP.PostPaperAudit EOS07GSP.PaperInterface EOS07GSP
```

After documentation-only edits, at least run:

```bash
git diff --check -- papers/EOS07GSP skills/econcs-formalizer README.md
```
