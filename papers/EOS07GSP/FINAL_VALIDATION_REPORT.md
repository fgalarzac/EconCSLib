# Final Validation Report: EOS07GSP

Updated: 2026-07-02

## 1. Human Verdict
The paper is formalized against the curated NBER source inventory. The compact
review surface covers the first-price and GSP/VCG examples, Remarks 1--3,
Definition 4, Lemmas 5--6, Theorem 7, the source proof-step claims for
Theorem 8, and the bundled Theorem 8 ex-post payoff-game endpoint.

Theorem 8 is formalized using the source theorem's ex-post payoff-game
interpretation rather than as a reusable general theory of continuous
belief-system PBE. In that source-facing game, the named continuous
dropout-price strategy is the unique payoff-PBE on the nonnegative source
support, and the induced finite source-event/belief-source-extensive witness
has the VCG-equivalent outcome. The finite source-event and belief witnesses
are generated internally from the source-facing strict ranked-value model.

## 2. Closeout Status
- Completion status: formalized.
- One-sentence recap: The curated NBER source inventory through Theorem 8 is covered by the compact paper-facing review surface.
- Lean footprint: 133,338 paper-local Lean LOC; `PaperInterface.lean` is 294 lines; 25 human-review declarations are exposed.
- Audit summary: paper coverage sidecar is not separately recorded; statement LLM-as-judge sidecar is not separately recorded; assumption provenance has 1 paper_assumption; source-record audit reports 2 boundary inputs and 0 recursion failures; holistic source-first audit PASS; DAG/source-json audit PASS in `docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`.

## 3. Source and Scope
- Paper: *Internet Advertising and the Generalized Second-Price Auction:
  Selling Billions of Dollars Worth of Keywords*
- Authors: Benjamin Edelman, Michael Ostrovsky, and Michael Schwarz
- Source version: NBER Working Paper 11765, November 2005, with the AER 2007
  publication citation recorded in the folder metadata
- Source URL: <https://www.nber.org/papers/w11765>
- Lean folder: `papers/EOS07GSP`
- Human-facing theorem file: `papers/EOS07GSP/PaperInterface.lean`
- Exhaustive audit ledger: `papers/EOS07GSP/PostPaperAudit.lean`
- DAG artifacts: `papers/EOS07GSP/docs/DependencyDAG.tex` and
  `papers/EOS07GSP/docs/DependencyDAG.pdf`
- Lean footprint: tracked in `papers/EOS07GSP/status.json`; the compact review
  surface currently has 25 statement rows plus 1 source-condition row.

The folder tracks the NBER working-paper numbering: Remarks 1--3, Definition
4, Lemmas 5--6, and Theorems 7--8. A later public PDF renumbers analogous main
results, so this report uses the NBER numbering consistently.

## 4. Researcher Summary of Checked Results
- The first-price instability example has a compact arithmetic row showing the
  displayed profitable bid revisions.
- The GSP/VCG position-auction interface, locally envy-free outcomes, stable
  assignments, and the GSP/VCG running two-slot example are formalized.
- Remark 1, Remark 2, and Remark 3 are formalized: GSP payments weakly dominate
  VCG payments at the same bids, VCG is truthful, and GSP is not dominant-
  strategy truthful.
- Lemma 5 is formalized. Lemma 6 is formalized for the source's `K > N`
  condition through the deterministic tie-broken ranked-GSP implementation used
  to make off-equilibrium reports total; strict constructed profiles have no
  equilibrium ties.
- Theorem 7 is formalized, including the constructed `B*` outcome, payment
  identity, direct locally-envy-free equilibrium row, no-positive-transfer
  conclusion, and the strict tie-broken GSP comparison conclusion.
- Theorem 8 is formalized in the ex-post payoff-game/source-event form used by
  the source proof: the continuous dropout-price strategy satisfies the
  source-facing payoff-PBE predicate, every payoff-PBE in that modeled
  source-facing game agrees with it on the nonnegative source support, and the
  induced finite source-event and belief-source-extensive outcomes are
  VCG-equivalent.

## 5. Remaining Boundaries and Gaps
No paper-facing proof gaps are currently recorded for the curated NBER source
inventory. Saved human dashboard review remains pending and is separate from
Lean proof status.

## 6. Additional Assumptions Beyond Paper
None. The strict ranked-value model used by the Theorem 8 source-event
specialization is recorded as a source-condition row and audited as a
source-backed model primitive, not as an additional assumption beyond the
paper.

## 7. Proof-Strategy Deviations
None. Theorem 8 is formalized through the source theorem's ex-post payoff-game endpoint, and deterministic tie-breaking is used only to totalize finite ranked-GSP implementation statements whose source equilibrium profiles are strict.

## 8. Proof Tricks Worth Reusing
- Keep the human review surface close to the paper inventory. EOS uses 25
  statement rows for the source claims and proof-support rows, and keeps long
  proof-route variants in
  `PostPaperAudit.lean`.
- Separate source conditions from proof gaps. The strict ranked-value model is
  audited as a source primitive rather than left as an opaque theorem
  certificate.
- For dynamic auction results stated ex post, first prove the local payoff-game
  theorem and then connect it to the finite source-event outcome; this avoids
  introducing belief machinery that the source theorem does not use at the
  payoff-comparison step.

## 9. Mathematical Typos or Other Fixes Suggested in the Source Paper
None found.

## 10. Paper Issues or Caveats
None found.

## 11. Detailed Formalization Evidence
The formalization is organized around a compact paper interface and an
exhaustive audit ledger. `PaperInterface.lean` exposes source-facing rows for
the definitions, examples, lemmas, and main theorems. `PostPaperAudit.lean`
keeps the longer implementation ledger, including support lemmas and alternate
route endpoints that are useful for audit but too detailed for human review.

The current machine-readable audit artifacts report:

- Source-to-dashboard coverage: 24/24 source statements covered directly.
- Row-local LLM-as-judge statement translation: 25/25 rows match.
- Assumption/source-condition provenance: 1 source-condition row, current.
- Human dashboard review: 0/26 saved human rows.

## 12. Paper Assumption Provenance
The paper-facing interface has one source-condition row.

| Assumption declaration | Lean declaration | Source location / statement | Assumption validators | Comments |
| --- | --- | --- | --- | --- |
| Strict ordered value model | `assumption_theorem8_strict_ordered_value_certificate` | NBER source text around the ranked click-through-rate and value model assumptions | `codex-gpt-5.5-semantic-rejudge`, `paper_assumption` | This records the paper source primitives for the strict finite source-event specialization of Theorem 8. |

## 13. Displayed Formula Provenance
The main displayed formulas used in the paper-facing results are exposed in
`PaperInterface.lean` and checked by row-local statement judgments.

| Paper formula / subclaim | Lean declaration | Provenance | Validators | Comments |
| --- | --- | --- | --- | --- |
| Theorem 7 `B*` payment identity | `theorem7_bstar_payment_identity` | Derived in Lean from the ranked finite VCG-tail definitions | `codex-gpt-5.5-semantic-audit` | Matches the NBER source construction. |
| Theorem 8 dropout price formula | `theorem8_dropout_formula_eq_bstar_threshold` | Derived in Lean from the indifference-price formula and finite `B*` threshold | `codex-gpt-5.5-semantic-audit` | Matches the paper's displayed dropout-price formula. |
| Theorem 8 strict dropping-after-`q` payoff comparison | `theorem8_q_step1_dropping_after_q_review` | Derived in Lean from the source payoff comparison model | `codex-gpt-5.5-semantic-audit` | Captures the proof-line deviation above the indifference price. |
| Theorem 8 strict waiting-before-`q` payoff comparison | `theorem8_q_step2_waiting_before_q_review` | Derived in Lean from the source payoff comparison model | `codex-gpt-5.5-semantic-audit` | Captures the proof-line deviation below the indifference price. |

## 14. Library Lift Pass
Reusable position-auction, GSP, VCG-payment, locally-envy-free, stable-
assignment, and generalized-English payoff-game primitives live under
`EconCSLib/MechanismDesign/Auctions`. No additional library extraction is
required for closeout; future cleanup can continue reducing EOS-specific proof
aliases in `PostPaperAudit.lean`.

## 15. DAG Audit
- DAG source: `DependencyDAG.tex`
- Rendered artifact: `DependencyDAG.pdf`
- Topology: the DAG contains the NBER source inventory: Remarks 1--3,
  Definition 4, Lemmas 5--6, and Theorems 7--8.
- Layout: the DAG is rendered as a standalone PDF and visually inspected for
  box overlap, legend overlap, and arrow routing after closeout edits.

## 16. Validation Checks
The closeout validation path for this report is:

- `lake build EOS07GSP`
- `python3 scripts/review_dashboard.py --paper EOS07GSP --statement-precheck`
- `python3 scripts/review_dashboard.py --paper EOS07GSP --source-to-lean-precheck`
- `python3 scripts/review_dashboard.py --paper EOS07GSP --assumption-precheck`
- `python3 scripts/audit_repository.py --paper EOS07GSP --paper-closeout --include-active --info-limit 0`

The final command is the targeted repository audit command required for this
paper's closeout gate.

## 17. Paper Definitions Checked
- Locally envy-free equilibrium: Definition 4's adjacent no-envy equilibrium
  predicate. Lean: `definition4_locally_envy_free`.
- Stable assignment: the Shapley-Shubik assignment-game no-profitable-rematch
  predicate used by Lemmas 5--6. Lean: `stable_assignment`.
- Theorem 7 `B*` bid/payment construction: the ranked finite GSP profile and
  VCG-tail payment identity. Lean: `theorem7_bstar_payment_identity`.
- Theorem 8 dropout-price formula: the continuous generalized-English
  indifference price and its finite `B*` threshold specialization. Lean:
  `theorem8_dropout_formula_eq_bstar_threshold`.

## 18. Named Theorem Statements Checked
### Remarks 1--3
**Paper statement.** Same-bid GSP payments weakly dominate VCG payments,
truth-telling is dominant under VCG, and truth-telling is not dominant under
GSP.

**Lean interface statement.**
- `remark1_gsp_payments_weakly_dominate_vcg`
- `remark2_vcg_truthful`
- `remark3_gsp_not_truthful`

**Status.** formalized.

### Running Example
**Paper statement.** The two-slot, three-bidder first-price example has
profitable bid revisions; the GSP/VCG example has truthful GSP bids as a Nash
equilibrium and GSP revenue higher than VCG revenue.

**Lean interface statement.**
- `first_price_running_example_profitable_revision_chain`
- `running_example_truthful_gsp_nash`
- `running_example_truthful_gsp_revenue_comparison`

**Status.** formalized.

### Lemma 5
**Paper statement.** The outcome of any locally envy-free equilibrium is a
stable assignment.

**Lean interface statement.**
- `lemma5_locally_envy_free_stable`

**Status.** formalized.

### Lemma 6
**Paper statement.** Any stable assignment is an outcome of a locally
envy-free GSP equilibrium.

**Lean interface statement.**
- `lemma6_tiebreak_ranked_gsp_stable_assignment_locally_envy_free`

**Status.** formalized.

### Theorem 7
**Paper statement.** The constructed `B*` equilibrium yields the same positions
and payments as VCG and is revenue-minimal among locally envy-free equilibria.

**Lean interface statement.**
- `theorem7_ranked_gsp_bstar_mechanism_realizes_bstar_outcome`
- `theorem7_bstar_payment_identity`
- `theorem7_bstar_locally_envy_free`
- `theorem7_no_positive_transfer_conclusion`
- `theorem7_strict_tiebreak_gsp_comparison_conclusion`

**Status.** formalized.

### Theorem 8
**Paper statement.** The generalized-English auction has a unique continuous-
strategy perfect Bayesian equilibrium with the displayed dropout-price formula;
the equilibrium is ex post and yields VCG-equivalent positions and payoffs.

**Lean interface statement.**
- `theorem8_dropout_formula_eq_bstar_threshold`
- `theorem8_q_step1_dropping_after_q_review`
- `theorem8_q_step2_waiting_before_q_review`
- `theorem8_continuous_generalized_english_payoff_game_strict_values_main_conclusion_review`

**Status.** formalized under the source theorem's ex-post payoff-game reading.

## 19. Paper-Facing Statement Validator Ledger
The tracked validator sidecars are current for the compact review surface:
25 statement rows match their source statements or proof-support review
statements, 24 source-inventory items are covered directly, and one
source-condition row is source-backed. The row-level validator is
`codex-gpt-5.5-semantic-audit` or `codex-gpt-5.5-semantic-rejudge` depending
on the row refresh date. Human dashboard review remains 0/26 saved rows.
