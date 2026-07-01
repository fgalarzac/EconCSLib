# Agent Source Audit: EOS07GSP

## Overall status: PASS

This is a source-first audit of the current EOS07GSP formalization. The local
NBER source text was read first, then compared against
`paper_statement_map.json`, `PaperInterface.lean`, the LLM-as-judge sidecars,
and `FINAL_VALIDATION_REPORT.md`.

This is the holistic audit lane: it is not a replacement for the structured
sidecars, but a source-to-interface reading pass intended to catch omissions
that a row-local statement judge can miss.

## Source Inventory

The local NBER source text contains the following main source-facing targets:

- Section 2.2 first-price running example: the two-slot, three-bidder example
  has profitable successive bid revisions and illustrates first-price
  instability.
- Section 2.2--2.3 GSP/VCG running example: truthful GSP bids are a Nash
  equilibrium in the concrete example; GSP payments are 800 and 200; VCG
  payments are 600 and 200; GSP revenue exceeds VCG revenue.
- Remark 1: same-bid GSP payments weakly dominate VCG payments.
- Remark 2: truth-telling is a dominant strategy under VCG.
- Remark 3: truth-telling is not a dominant strategy under GSP.
- Definition 4: locally envy-free equilibrium of the static GSP game.
- Lemma 5: every locally envy-free GSP equilibrium outcome is a stable
  assignment.
- Lemma 6: if the number of bidders is greater than the number of positions,
  any stable assignment is an outcome of a locally envy-free GSP equilibrium.
- Theorem 7: the `B*` strategy profile is a locally envy-free equilibrium, has
  the VCG-equivalent position/payment outcome, and is seller-revenue-minimal
  among locally envy-free equilibria.
- Theorem 8: the generalized English auction has a unique perfect Bayesian
  equilibrium in continuous strategies with the displayed dropout-price
  formula; the equilibrium yields VCG-equivalent positions/payoffs and is
  ex post.

## Lean Interface Comparison

The compact interface now covers all source inventory items above. In
particular:

- `first_price_running_example_profitable_revision_chain` covers the
  first-price profitable revision chain.
- `lemma6_tiebreak_ranked_gsp_stable_assignment_locally_envy_free` covers
  Lemma 6 for the source's `K > N` condition.
- `theorem7_bstar_locally_envy_free` exposes the direct source subclaim that
  the constructed `B*` profile is locally envy-free.
- `theorem8_continuous_generalized_english_payoff_game_strict_values_main_conclusion_review`
  covers Theorem 8 under the source theorem's ex-post payoff-game reading.
- `theorem8_belief_source_extensive_unique_pbe_vcg_conclusion` is a
  proof-support review row showing that the finite belief-source-extensive
  route is generated internally from source-facing strict ranked values rather
  than supplied as a replay certificate.

## Machine Audit Results

- Source-to-dashboard coverage: 24/24 source statements covered directly.
- Row-local statement matching: 25/25 row-local statement judgments match.
- Assumption/source-condition provenance: 1 source-condition row, source-backed.
- Source-record audit: the support-boundary input in the continuous support
  uniqueness row is universally quantified and Lean-proved for every boundary
  function; the strict ranked-value model is source-backed by the paper's
  click-through-rate and value-distribution primitives.
- Lean build: `lake build EOS07GSP` succeeds.

## Findings

No unresolved paper-facing proof gaps are recorded for the curated NBER source
inventory. The strict ranked-value model used by the Theorem 8 source-event
specialization is a source-condition row, not an additional assumption beyond
the paper.

## Why This Audit Was Needed

An earlier automated coverage pass used a narrower source inventory and missed
the first-price example, the general Lemma 6 scope, and the direct Theorem 7
locally-envy-free subclaim. This artifact records the corrected source-first
pass so future closeout work starts from the paper inventory rather than from
whatever rows already happen to be exposed.
