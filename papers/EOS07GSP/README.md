# Internet Advertising and the Generalized Second-Price Auction

## Source Version

- Paper: *Internet Advertising and the Generalized Second-Price Auction: Selling Billions of Dollars Worth of Keywords*
- Authors: Benjamin Edelman, Michael Ostrovsky, and Michael Schwarz
- Version checked locally: NBER Working Paper 11765, November 2005; folder name follows the 2007 AER publication citation
- NBER URL: https://www.nber.org/papers/w11765
- Published DOI: https://doi.org/10.1257/aer.97.1.242

The PDF is cached locally as `EOS07GSP.pdf` and ignored by the paper-folder
`.gitignore`. The extracted text cache `EOS07GSP.txt` is used for
named-statement searches; refresh it only if the source PDF changes.

Refresh check: on 2026-05-16, `EOS07GSP.pdf` and `EOS07GSP.txt` were compared
against the online NBER PDF at `https://www.nber.org/papers/w11765.pdf` and
matched exactly. A Stanford-hosted later/final PDF was also inspected; it
renumbers the analogous main source results as Theorems 1--2, while this
folder continues to track the NBER-numbered working-paper source with Theorems
7--8.

Initial NBER source inventory for the DAG: Remarks 1--3, Definition 4, Lemmas
5--6, and Theorems 7--8.

## Central Theorem File

- `EOS07GSP/MainTheorems.lean`
- `EOS07GSP/PaperInterface.lean`
- `EOS07GSP/PostPaperAudit.lean`
- `FINAL_VALIDATION_REPORT.md`
- `START_HERE_NEXT_AGENT.md`
- `THEOREM8_FINISH_STRATEGY.md`
- `HANDOFF_2026-05-06.md`

Reusable position-auction and GSP primitives live in
`EconCSLib/MechanismDesign/Auctions`.

`PaperInterface.lean` is the compact human-facing review surface: it exposes
the GSP counterexample, running example, Lemmas 5--6, Theorem 7, and Theorem 8
as source-facing rows. Theorem 8 is represented through the source theorem's
ex-post payoff-game reading: the named continuous dropout-price strategy is a
payoff-PBE, every payoff-PBE agrees with it on the nonnegative source support,
and every payoff-PBE induces the finite source-event PBE with VCG outcome.
`PostPaperAudit.lean` remains the exhaustive declaration ledger for detailed
helper endpoints and alternate proof routes.

## Handoff note

Start future EOS work from `FINAL_VALIDATION_REPORT.md` and
`POST_FORMALIZATION_AUDIT.md`. The older handoff files remain available as
historical proof-route ledgers, but they are no longer the current status
source.

## Theorem Status

| Paper item | Lean interface declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
| Position-auction interface and GSP truthfulness predicates | `definition4_locally_envy_free`, `stable_assignment`, `remark2_vcg_truthful` | formalized | `PaperInterface.lean`, `EconCSLib/MechanismDesign/Auctions/Position.lean` | None |
| Remark 1, same bids produce weakly higher GSP payments than VCG payments | `remark1_gsp_payments_weakly_dominate_vcg` | formalized | `PaperInterface.lean` | None |
| Remark 2, truth-telling is a dominant strategy under VCG | `remark2_vcg_truthful` | formalized | `PaperInterface.lean` | None |
| Remark 3, truth-telling is not a dominant strategy under GSP | `remark3_gsp_not_truthful` | formalized | `PaperInterface.lean` | None |
| Running GSP/VCG example | `running_example_truthful_gsp_nash`, `running_example_truthful_gsp_revenue_comparison` | formalized | `PaperInterface.lean` | None |
| Definition 4, locally envy-free equilibrium | `definition4_locally_envy_free` | formalized | `PaperInterface.lean` | None |
| Lemma 5, locally envy-free equilibrium gives stable assignment | `lemma5_locally_envy_free_stable` | formalized | `PaperInterface.lean` | None |
| Lemma 6, stable assignment gives locally envy-free outcome | `lemma6_tiebreak_ranked_gsp_stable_assignment_locally_envy_free` | formalized | `PaperInterface.lean` | None |
| Theorem 7, a locally envy-free equilibrium with VCG-equivalent payoffs and revenue-minimality | `theorem7_ranked_gsp_bstar_mechanism_realizes_bstar_outcome`, `theorem7_bstar_payment_identity`, `theorem7_no_positive_transfer_conclusion`, `theorem7_strict_tiebreak_gsp_comparison_conclusion` | formalized | `PaperInterface.lean` | None |
| Theorem 8, generalized-English auction unique ex-post payoff-game PBE with VCG-equivalent outcome | `theorem8_dropout_formula_eq_bstar_threshold`, `theorem8_q_step1_dropping_after_q_review`, `theorem8_q_step2_waiting_before_q_review`, `theorem8_continuous_generalized_english_payoff_game_strict_values_main_conclusion_review` | formalized | `PaperInterface.lean` | None; the strict ranked-value model is tracked as a source-condition row in `Assumptions.lean`. |

Detailed helper endpoints and alternate proof routes remain in `PostPaperAudit.lean`.

## Source-Audit Notes

The curated source inventory is recorded in `paper_statement_map.json` and is
based on the local NBER source text cache. It contains 24 source-facing
statement rows covering the first-price and GSP/VCG examples, Remarks 1--3,
Definition 4, Lemmas 5--6, Theorem 7, Theorem 8 proof-step claims, and the
bundled Theorem 8 ex-post payoff-game endpoint. `paper_coverage_llm.json`
records 24/24 source statements covered by dashboard rows, and
`statement_match_llm.json` records 25/25 row-local statement matches,
including the proof-support belief-source-extensive Theorem 8 row.

`Assumptions.lean` contains one source-condition row,
`assumption_theorem8_strict_ordered_value_certificate`. Its provenance is
recorded in `assumption_match_llm.json` as a source-backed model primitive for
the paper source strict ranked-value/source-event specialization of Theorem 8.
This is not an additional assumption beyond the paper.

`PostPaperAudit.lean` is the exhaustive importable Lean ledger for helper
endpoints and alternate proof routes. The human-facing status is summarized in
`FINAL_VALIDATION_REPORT.md`, `DependencyDAG.tex`, and `PaperInterface.lean`.
