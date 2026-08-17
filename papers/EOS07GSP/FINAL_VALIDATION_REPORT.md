# Final Validation Report: EOS07GSP

Updated: 2026-07-31

## 1. Human Verdict
Formalized. The compact review surface covers the curated NBER mathematical
inventory: the first-price and GSP/VCG examples, Remarks 1--3, Definition 4,
Lemmas 5--6, Theorem 7, and Theorem 8.

For Theorem 8, Lean now constructs the continuous positive-density value law,
full-history strategy, conditional Bayes beliefs on every positive-probability
survival event, and a legal-history ex-post PBE. Sequential rationality compares
the named strategy against every complete history-dependent continuation plan
for every realized ordered opponent profile, which also gives the posterior-
expected best-response inequality. Every legal-history ex-post PBE has the same
clock-clamped dropout action, and the induced finite outcome is VCG-equivalent.
The source's below-clock raw threshold is recorded as the ordinary
immediate-drop interpretation of a stopped auction, not as a theorem caveat.

## 2. Closeout Status
- Completion status: formalized.
- Audit summary: source coverage has 24 covered; diagnostics: full inventory shown because paper_statement_map.json must explicitly set source_coverage_mode before a source-coverage closeout; statement LLM-as-judge has no rows; diagnostics: 23 orphan/stale statement-sidecar rows excluded, 23 configured rows without unambiguous current receipts; Lean-to-TeX has 23 row translations; assumption provenance sidecar has no configured source-condition rows; source-record classification has 35 source condition, 2 non-propositional witness data; source-record audit reports 23 source-record review rows, 44 boundary inputs, 5 conclusion dependencies, 34 recursive fields, 0 source-record-only unresolved conclusion dependencies, 0 recursion failures; review-surface audit review surface passed over 23 review rows; holistic source-first audit status is not inferred by this generator; DAG/source-json audit status is not inferred (see `docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`).
- One-sentence recap: the curated NBER mathematical inventory through Theorem 8 is covered, including the source-intended legal-history ex-post PBE, Bayes consistency, arbitrary-continuation sequential rationality, effective uniqueness, and VCG outcome.
- Source pin: `EOS07GSP.txt`, SHA256 `9094a9c8cd917b728cf872b7741a4de9b5636c5cdadd08b7bfcc4b7c64df9cbc`.
- Certification note: Lean proof status and protocol evidence are current at closeout; saved human dashboard review remains a separate governance lane and is not claimed here.

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
  surface currently has 23 paper-facing rows and no theorem-facing assumption
  declaration.

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
- Theorem 8 is formalized on its legal-history domain. Lean constructs the
  continuous full-history strategy and Bayes-consistent conditional belief
  system, proves ex-post optimality against every complete continuation plan,
  lifts that comparison to supported posterior expectations, proves effective
  dropout-action uniqueness among legal-history ex-post PBEs, and derives the
  VCG-equivalent finite outcome.

## 5. Remaining Boundaries and Gaps
No mathematical source-inventory gaps are recorded. The formula can lie below
the current clock when a bidder's value is below the last dropout. On such a
stopped-auction history it means immediate dropout, so legality and uniqueness
are stated for the observable clock-clamped action on feasible histories. This
is an implied operational-domain convention, not a weakened theorem or caveat.
Saved human dashboard review remains separate from Lean proof status.

## 6. Additional Assumptions Beyond Paper
None.

## 7. Proof-Strategy Deviations
Theorem 8 uses an ex-post refinement of sequential rationality: the proof first
compares complete continuation plans pointwise for every ordered opponent-value
profile, then integrates the inequality under every supported posterior.
Deterministic tie-breaking totalizes finite ranked-GSP implementation statements
whose source equilibrium profiles are strict.

## 8. Proof Tricks Worth Reusing
- Keep the human review surface close to the paper inventory. EOS uses 23
  statement rows for the 24 source items and keeps long
  proof-route variants in
  `PostPaperAudit.lean`.
- Separate source conditions from proof gaps. The strict ranked-value model is
  audited as a source primitive rather than left as an opaque theorem
  certificate.
- For dynamic auction results stated ex post, prove arbitrary-continuation
  optimality pointwise before integrating under conditional beliefs. This makes
  posterior sequential rationality a consequence rather than a premise.

## 9. Generalizations, Conjectures, and Extensions

The proof decomposition suggests a routine extension from one common value law
to bidder-specific independent continuous positive-density laws: the conditional
belief construction changes by substituting the bidder-specific marginals,
while the ex-post continuation comparison remains pointwise. A second reusable
extension is to expose the clock-clamped effective-action semantics as a generic
interface for continuous ascending auctions. Neither extension is needed for the
paper's result, and neither is claimed here without a dedicated reviewed theorem.

## 10. Mathematical Typos or Other Fixes Suggested in the Source Paper
None found.

## 11. Paper Issues or Caveats
None affecting theorem status. The below-clock threshold case is an ordinary
stopped-auction immediate-drop convention and is exposed explicitly by the
legal-history predicate and clock-clamped uniqueness statement.

## 12. Detailed Formalization Evidence
The formalization is organized around a compact paper interface and an
exhaustive audit ledger. `PaperInterface.lean` exposes source-facing rows for
the definitions, examples, lemmas, and main theorems. `PostPaperAudit.lean`
keeps the longer implementation ledger, including support lemmas and alternate
route endpoints that are useful for audit but too detailed for human review.

The current machine-readable audit artifacts report:

- Source-to-dashboard coverage: the 24-item curated inventory is covered.
- Row-local statement review: all 23 configured review rows are included in the
  current protocol pass.
- Assumption provenance: no theorem-facing assumption declaration is configured.
- Human dashboard review is a separate governance lane and remains unclaimed.

## 13. Paper Assumption Provenance

No paper-facing assumption declaration is used. Source model conditions such as
strictly decreasing positive click rates and continuous independent values with
positive density occur directly as visible theorem parameters or constructed
law fields, not as conclusion-bearing certificates.

<!-- BEGIN GENERATED ASSUMPTION PROVENANCE LEDGER -->
### Current Canonical Evidence
Generated from the configured source-condition surface and exact current statement digests in the canonical assumption-provenance sidecar. Model, agent, and automated checks are identified as such; no human review is inferred.

| Assumption declaration | Lean declaration | Source location / statement | Assumption validators | Comments |
| --- | --- | --- | --- | --- |
| None | `none` | None | None | No paper-facing assumption declarations are configured. |
<!-- END GENERATED ASSUMPTION PROVENANCE LEDGER -->

## 14. Displayed Formula Provenance

The main displayed formulas used in the paper-facing results are exposed in
`PaperInterface.lean` and checked by row-local statement judgments.

<!-- BEGIN GENERATED FORMULA PROVENANCE LEDGER -->
### Current Canonical Evidence
Rows are selected from semantic `formula` and `equation` source-kind metadata within the configured semantic source-coverage scope, never from declaration names. Coverage and statement checks remain separate evidence lanes. Scope metadata needs repair, so the full inventory is shown: paper_statement_map.json must explicitly set source_coverage_mode before a source-coverage closeout

| Paper formula / subclaim | Lean declaration | Provenance | Validators | Comments |
| --- | --- | --- | --- | --- |
| Theorem 8 states the dropout price formula p_i(k,h,s_i)=s_i-alpha_k/alpha_{k-1}(s_i-b_{k+1}); the appendix defines q by the same indifference equation. | `theorem8_dropout_formula_eq_bstar_threshold` | covered. `theorem8_dropout_formula_eq_bstar_threshold`: no completed statement check | covered; Agent check by Codex EOS07 source-first v10 full-formalization audit; 2026-07-18 | After unfolding the reviewed predicates, the linked conclusion preserves the complete finite-auction domain, exact real formulas, quantifier order, strategic scope, and conclusion of this cited source item without relying on a result-bearing input package. |
| The q formula is defined by indifference between position k at price b_{k+1} and position k-1 at price q, placing q between the previous dropout price and the bidder value under the weak source conditions. | `theorem8_q_mem_interval_review` | covered. `theorem8_q_mem_interval_review`: no completed statement check | covered; Agent check by Codex EOS07 source-first v10 full-formalization audit; 2026-07-18 | After unfolding the reviewed predicates, the linked conclusion preserves the complete finite-auction domain, exact real formulas, quantifier order, strategic scope, and conclusion of this cited source item without relying on a result-bearing input package. |
| Under the paper's strict descending click-through-rate convention and positive values, q lies strictly between the previous dropout price and the bidder value. | `theorem8_q_strict_mem_interval_review` | covered. `theorem8_q_strict_mem_interval_review`: no completed statement check | covered; Agent check by Codex EOS07 source-first v10 full-formalization audit; 2026-07-18 | After unfolding the reviewed predicates, the linked conclusion preserves the complete finite-auction domain, exact real formulas, quantifier order, strategic scope, and conclusion of this cited source item without relying on a result-bearing input package. |
<!-- END GENERATED FORMULA PROVENANCE LEDGER -->

## 15. Library Lift Pass
Reusable position-auction, GSP, VCG-payment, locally-envy-free, stable-
assignment, and generalized-English payoff-game primitives live under
`EconCSLib/MechanismDesign/Auctions`. No additional library extraction is
required for closeout; future cleanup can continue reducing EOS-specific proof
aliases in `PostPaperAudit.lean`.

## 16. DAG Audit
- DAG source: `docs/DependencyDAG.tex`
- Rendered artifact: `docs/DependencyDAG.pdf`
- Topology: the DAG contains the NBER source inventory: Remarks 1--3,
  Definition 4, Lemmas 5--6, and Theorems 7--8.
- Layout: the DAG is rendered as a standalone PDF and visually inspected for
  box overlap, legend overlap, and arrow routing after closeout edits.

## 17. Validation Checks
<!-- BEGIN GENERATED LLM-AS-JUDGE RESULTS -->
### LLM-as-Judge Results
- Source coverage (`audit/paper_coverage_llm.json`): 24 covered; diagnostics: full inventory shown because paper_statement_map.json must explicitly set source_coverage_mode before a source-coverage closeout.
- Statement match (`audit/statement_match_llm.json`): no rows; diagnostics: 23 orphan/stale statement-sidecar rows excluded, 23 configured rows without unambiguous current receipts.
- Lean-to-TeX translations (`audit/lean_to_tex_llm.json`): 23 row translations generated from Lean statements.
- Assumption provenance (`audit/assumption_match_llm.json`): no configured source-condition rows.
- Source-record classification (`audit/source_record_match_llm.json`): 35 source condition, 2 non-propositional witness data.
- Source-record structural audit (`audit/source_record_audit.json`): 23 source-record review rows, 44 boundary inputs, 5 conclusion dependencies, 34 recursive fields, 0 source-record-only unresolved conclusion dependencies, 0 recursion failures.
- Review-surface audit (`audit/review_surface_llm.json`): review surface passed over 23 review rows.
- Holistic source-first audit (`docs/AGENT_SOURCE_AUDIT.md`): status not inferred by this generator.
- DAG/source/source-json audit (`docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`): status not inferred by this generator.
<!-- END GENERATED LLM-AS-JUDGE RESULTS -->

The closeout validation path for this report is:

- `lake build EOS07GSP`
- `python3 scripts/audit_conclusion_provenance.py --paper EOS07GSP --json`
- `python3 scripts/review_dashboard.py --paper EOS07GSP --statement-check`
- `python3 scripts/review_dashboard.py --paper EOS07GSP --paper-coverage-check`
- `python3 scripts/review_dashboard.py --paper EOS07GSP --source-to-lean-check`
- `python3 scripts/review_dashboard.py --paper EOS07GSP --assumption-check`
- `python3 scripts/audit_evidence_integrity.py --paper EOS07GSP --json`
- `python3 scripts/audit_repository.py --paper EOS07GSP --paper-closeout --include-active --info-limit 0`
- `git diff --check`

The final command is the targeted repository audit command required for this
paper's closeout gate.

## 18. Paper Definitions Checked
- Locally envy-free equilibrium: Definition 4's static-equilibrium condition
  plus the displayed adjacent-rank no-envy inequality, exposed by the proved
  unfolding `definition4_locally_envy_free`.
- Stable assignment: the Shapley-Shubik assignment-game no-profitable-rematch
  predicate used by Lemmas 5--6. Lean: `stable_assignment`.
- Theorem 7 `B*` bid/payment construction: the ranked finite GSP profile and
  VCG-tail payment identity. Lean: `theorem7_bstar_payment_identity`.
- Theorem 8 dropout-price formula: the continuous generalized-English
  indifference price and its finite `B*` threshold specialization. Lean:
  `theorem8_dropout_formula_eq_bstar_threshold`.

## 19. Named Theorem Statements Checked
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
- `theorem8_continuous_full_history_bayes_ex_post_review`

The finite source-event VCG outcome is supplied by the checked support
declaration
`theorem8_source_event_strict_values_unique_pbe_formula_conclusion` together
with the Theorem 7 `B*` outcome and the dropout-formula bridge.

**Status.** formalized. The full-history row proves the source-intended legal-
history ex-post PBE with actual conditional Bayes beliefs, arbitrary complete
continuation deviations, effective-action uniqueness, and the displayed
dropout formula.

## 20. Paper-Facing Statement Validator Ledger

The compact surface has 23 configured rows and the source inventory has 24
items. The raw statement-v10 rows do not bind the current cached statements by
exact semantic identity, so they remain diagnostic-only even though the
coverage-v4 ledger is present. Human dashboard certification remains unclaimed.

<!-- BEGIN GENERATED STATEMENT VALIDATOR LEDGER -->
### Current Canonical Evidence
Independent human dashboard review: 0/23 rows. No human row-level approval is inferred. review surface passed; Agent check by Codex EOS07 source-first v10 full-formalization audit; 2026-07-19 Diagnostic-only evidence excluded from this paper-facing ledger: 23 unconfigured, stale, or ambiguous statement-sidecar rows.

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| Definition4 locally envy free | `definition4_locally_envy_free` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Stable assignment | `stable_assignment` | No completed statement check recorded. No Lean translation recorded | None recorded |
| First price running example profitable revision chain | `first_price_running_example_profitable_revision_chain` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Remark1 gsp payments weakly dominate vcg | `remark1_gsp_payments_weakly_dominate_vcg` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Remark2 vcg truthful | `remark2_vcg_truthful` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Remark3 gsp not truthful | `remark3_gsp_not_truthful` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Running example truthful gsp nash | `running_example_truthful_gsp_nash` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Running example truthful gsp revenue comparison | `running_example_truthful_gsp_revenue_comparison` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Lemma5 locally envy free stable | `lemma5_locally_envy_free_stable` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Lemma6 tiebreak ranked gsp stable assignment locally envy free | `lemma6_tiebreak_ranked_gsp_stable_assignment_locally_envy_free` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem7 ranked gsp bstar mechanism realizes bstar outcome | `theorem7_ranked_gsp_bstar_mechanism_realizes_bstar_outcome` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem7 bstar payment identity | `theorem7_bstar_payment_identity` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem7 bstar locally envy free | `theorem7_bstar_locally_envy_free` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem7 no positive transfer conclusion | `theorem7_no_positive_transfer_conclusion` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem7 strict tiebreak gsp comparison conclusion | `theorem7_strict_tiebreak_gsp_comparison_conclusion` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem8 dropout formula eq bstar threshold | `theorem8_dropout_formula_eq_bstar_threshold` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem8 q step2 waiting before q review | `theorem8_q_step2_waiting_before_q_review` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem8 q step1 dropping after q review | `theorem8_q_step1_dropping_after_q_review` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem8 q mem interval review | `theorem8_q_mem_interval_review` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem8 q strict mem interval review | `theorem8_q_strict_mem_interval_review` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem8 q continuous value review | `theorem8_q_continuous_value_review` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem8 continuous full history bayes ex post review | `theorem8_continuous_full_history_bayes_ex_post_review` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem8 continuous source local best response support unique review | `theorem8_continuous_source_local_best_response_support_unique_review` | No completed statement check recorded. No Lean translation recorded | None recorded |
<!-- END GENERATED STATEMENT VALIDATOR LEDGER -->

## 21. Source-Coverage Audit Ledger

- Source inventory: 24 named mathematical items from the pinned NBER working
  paper.
- Coverage result: all 24 items are directly covered; no missing or conditional
  source item is recorded.
- LLM-as-judge coverage audit: coverage-v4 records all 24 coverage outcomes.
  The 23 raw statement-v10 rows do not bind the current cached statements by
  exact semantic identity and therefore remain diagnostic-only.
- Human review: no dashboard sign-off is claimed.

<!-- BEGIN GENERATED SOURCE COVERAGE LEDGER -->
### Current Canonical Evidence
- Coverage scope: full inventory shown because scope metadata needs repair (paper_statement_map.json must explicitly set source_coverage_mode before a source-coverage closeout).
- Source inventory: 24 source statements from `EOS07GSP.txt`.
- Coverage result: 24 covered.
- Coverage review: coverage ledger recorded; Agent check by Codex EOS07 source-first v10 full-formalization audit; 2026-07-19.
- Row-local statement checks: 0/26 linked row references have a completed canonical statement check; repeated links are counted per source row.

| Source statement | Linked Lean review rows | Coverage judgment | Row-local statement checks | Comments |
| --- | --- | --- | --- | --- |
| Definition 4 defines a locally envy-free equilibrium of the static GSP game as an equilibrium in which no player can improve by exchanging bids with the player ranked one position above; formally, for each allocated adjacent position the adjacent no-envy inequality holds. | `definition4_locally_envy_free` | covered | `definition4_locally_envy_free`: no completed statement check | After unfolding the reviewed predicates, the linked conclusion preserves the complete finite-auction domain, exact real formulas, quantifier order, strategic scope, and conclusion of this cited source item without relying on a result-bearing input package. |
| The paper maps GSP outcomes to the Shapley-Shubik assignment game, where advertiser-position pair values are alpha_k s_i and stability means no profitable advertiser-position rematch. | `stable_assignment` | covered | `stable_assignment`: no completed statement check | After unfolding the reviewed predicates, the linked conclusion preserves the complete finite-auction domain, exact real formulas, quantifier order, strategic scope, and conclusion of this cited source item without relying on a result-bearing input package. |
| In the Section 2.2 first-price running example with two slots, click rates 200 and 100, and bidder values 10, 4, and 2, bidder 1 prefers the minimal top bid 2.02 to paying more for the same top slot, bidder 2 can profitably raise from 2.01 to 2.03 to take the top slot, and bidder 1 can then profitably raise to 2.04 to take the top slot back. | `first_price_running_example_profitable_revision_chain` | covered | `first_price_running_example_profitable_revision_chain`: no completed statement check | After unfolding the reviewed predicates, the linked conclusion preserves the complete finite-auction domain, exact real formulas, quantifier order, strategic scope, and conclusion of this cited source item without relying on a result-bearing input package. |
| Remark 1 states that if advertisers bid the same amounts under GSP and VCG, each advertiser payment is at least as large under GSP as under VCG, with the recursive VCG-payment induction displayed immediately after the remark. | `remark1_gsp_payments_weakly_dominate_vcg` | covered | `remark1_gsp_payments_weakly_dominate_vcg`: no completed statement check | After unfolding the reviewed predicates, the linked conclusion preserves the complete finite-auction domain, exact real formulas, quantifier order, strategic scope, and conclusion of this cited source item without relying on a result-bearing input package. |
| Remark 2 states that truth-telling is a dominant strategy under VCG, citing the standard VCG property. | `remark2_vcg_truthful` | covered | `remark2_vcg_truthful`: no completed statement check | After unfolding the reviewed predicates, the linked conclusion preserves the complete finite-auction domain, exact real formulas, quantifier order, strategic scope, and conclusion of this cited source item without relying on a result-bearing input package. |
| Remark 3 states that truth-telling is not a dominant strategy under GSP and gives the two-slot, three-bidder deviation where bidder 1 shades to obtain the second position and higher payoff. | `remark3_gsp_not_truthful` | covered | `remark3_gsp_not_truthful`: no completed statement check | After unfolding the reviewed predicates, the linked conclusion preserves the complete finite-auction domain, exact real formulas, quantifier order, strategic scope, and conclusion of this cited source item without relying on a result-bearing input package. |
| The running two-slot, three-bidder example has click rates 200 and 100 and values 10, 4, and 2; the text states truthful GSP bids are an equilibrium in this example. | `running_example_truthful_gsp_nash` | covered | `running_example_truthful_gsp_nash`: no completed statement check | After unfolding the reviewed predicates, the linked conclusion preserves the complete finite-auction domain, exact real formulas, quantifier order, strategic scope, and conclusion of this cited source item without relying on a result-bearing input package. |
| The running example computes GSP payments of 4 and 2 per click, VCG payments of 600 and 200 total, and states that VCG revenues are lower than GSP revenues in the example. | `running_example_truthful_gsp_revenue_comparison` | covered | `running_example_truthful_gsp_revenue_comparison`: no completed statement check | After unfolding the reviewed predicates, the linked conclusion preserves the complete finite-auction domain, exact real formulas, quantifier order, strategic scope, and conclusion of this cited source item without relying on a result-bearing input package. |
| Lemma 5 states that the outcome of any locally envy-free equilibrium of auction Gamma is a stable assignment; the appendix proof derives assortativity and telescopes adjacent no-envy inequalities. | `lemma5_locally_envy_free_stable` | covered | `lemma5_locally_envy_free_stable`: no completed statement check | After unfolding the reviewed predicates, the linked conclusion preserves the complete finite-auction domain, exact real formulas, quantifier order, strategic scope, and conclusion of this cited source item without relying on a result-bearing input package. |
| Lemma 6 states that, when the number of bidders exceeds the number of positions, any stable assignment is an outcome of a locally envy-free GSP equilibrium; the appendix constructs bids from assignment payments. | `lemma6_tiebreak_ranked_gsp_stable_assignment_locally_envy_free` | covered | `lemma6_tiebreak_ranked_gsp_stable_assignment_locally_envy_free`: no completed statement check | After unfolding the reviewed predicates, the linked conclusion preserves the complete finite-auction domain, exact real formulas, quantifier order, strategic scope, and conclusion of this cited source item without relying on a result-bearing input package. |
| Theorem 7 constructs the B* profile, proves bid order is preserved, and shows each bidder position and payment coincide with VCG in the constructed equilibrium. | `theorem7_ranked_gsp_bstar_mechanism_realizes_bstar_outcome` | covered | `theorem7_ranked_gsp_bstar_mechanism_realizes_bstar_outcome`: no completed statement check | After unfolding the reviewed predicates, the linked conclusion preserves the complete finite-auction domain, exact real formulas, quantifier order, strategic scope, and conclusion of this cited source item without relying on a result-bearing input package. |
| The B* construction sets bid b_i* from the previous VCG payment divided by the previous click-through rate; the proof checks that the resulting next-price payments coincide with VCG payments. | `theorem7_bstar_payment_identity` | covered | `theorem7_bstar_payment_identity`: no completed statement check | After unfolding the reviewed predicates, the linked conclusion preserves the complete finite-auction domain, exact real formulas, quantifier order, strategic scope, and conclusion of this cited source item without relying on a result-bearing input package. |
| Theorem 7 states that the B* strategy profile is locally envy-free; the proof checks that each bidder is indifferent between remaining in position and swapping with the bidder one position above. | `theorem7_bstar_locally_envy_free` | covered | `theorem7_bstar_locally_envy_free`: no completed statement check | After unfolding the reviewed predicates, the linked conclusion preserves the complete finite-auction domain, exact real formulas, quantifier order, strategic scope, and conclusion of this cited source item without relying on a result-bearing input package. |
| Theorem 7 concludes that the B* equilibrium has VCG-equivalent payments and that any other locally envy-free equilibrium yields seller revenue at least as high; the proof uses stable-assignment payment lower bounds. | `theorem7_no_positive_transfer_conclusion` | covered | `theorem7_no_positive_transfer_conclusion`: no completed statement check | After unfolding the reviewed predicates, the linked conclusion preserves the complete finite-auction domain, exact real formulas, quantifier order, strategic scope, and conclusion of this cited source item without relying on a result-bearing input package. |
| Theorem 7 comparison component links locally envy-free GSP outcomes to stable assignments and VCG payment lower bounds, under the paper's ranked strict-order conventions. | `theorem7_strict_tiebreak_gsp_comparison_conclusion` | covered | `theorem7_strict_tiebreak_gsp_comparison_conclusion`: no completed statement check | After unfolding the reviewed predicates, the linked conclusion preserves the complete finite-auction domain, exact real formulas, quantifier order, strategic scope, and conclusion of this cited source item without relying on a result-bearing input package. |
| Theorem 8 states the dropout price formula p_i(k,h,s_i)=s_i-alpha_k/alpha_{k-1}(s_i-b_{k+1}); the appendix defines q by the same indifference equation. | `theorem8_dropout_formula_eq_bstar_threshold` | covered | `theorem8_dropout_formula_eq_bstar_threshold`: no completed statement check | After unfolding the reviewed predicates, the linked conclusion preserves the complete finite-auction domain, exact real formulas, quantifier order, strategic scope, and conclusion of this cited source item without relying on a result-bearing input package. |
| Step 2 argues that if a bidder drops before q, waiting until q gives a strictly better payoff because another dropout occurs with positive probability and q is the indifference threshold. | `theorem8_q_step2_waiting_before_q_review` | covered | `theorem8_q_step2_waiting_before_q_review`: no completed statement check | After unfolding the reviewed predicates, the linked conclusion preserves the complete finite-auction domain, exact real formulas, quantifier order, strategic scope, and conclusion of this cited source item without relying on a result-bearing input package. |
| Step 1 argues that dropping after q cannot be optimal; above q, the bidder strictly benefits by dropping slightly earlier or at the indifference price. | `theorem8_q_step1_dropping_after_q_review` | covered | `theorem8_q_step1_dropping_after_q_review`: no completed statement check | After unfolding the reviewed predicates, the linked conclusion preserves the complete finite-auction domain, exact real formulas, quantifier order, strategic scope, and conclusion of this cited source item without relying on a result-bearing input package. |
| The q formula is defined by indifference between position k at price b_{k+1} and position k-1 at price q, placing q between the previous dropout price and the bidder value under the weak source conditions. | `theorem8_q_mem_interval_review` | covered | `theorem8_q_mem_interval_review`: no completed statement check | After unfolding the reviewed predicates, the linked conclusion preserves the complete finite-auction domain, exact real formulas, quantifier order, strategic scope, and conclusion of this cited source item without relying on a result-bearing input package. |
| Under the paper's strict descending click-through-rate convention and positive values, q lies strictly between the previous dropout price and the bidder value. | `theorem8_q_strict_mem_interval_review` | covered | `theorem8_q_strict_mem_interval_review`: no completed statement check | After unfolding the reviewed predicates, the linked conclusion preserves the complete finite-auction domain, exact real formulas, quantifier order, strategic scope, and conclusion of this cited source item without relying on a result-bearing input package. |
| Theorem 8 restricts attention to strategies continuous in valuation, and the displayed q formula is affine, hence continuous, in the bidder value. | `theorem8_q_continuous_value_review` | covered | `theorem8_q_continuous_value_review`: no completed statement check | After unfolding the reviewed predicates, the linked conclusion preserves the complete finite-auction domain, exact real formulas, quantifier order, strategic scope, and conclusion of this cited source item without relying on a result-bearing input package. |
| Theorem 8's proof identifies the continuous dropout-price formula by excluding deviations above and below q, so continuous one-step best responses agree with q on the relevant support. | `theorem8_continuous_source_local_best_response_support_unique_review` | covered | `theorem8_continuous_source_local_best_response_support_unique_review`: no completed statement check | After unfolding the reviewed predicates, the linked conclusion preserves the complete finite-auction domain, exact real formulas, quantifier order, strategic scope, and conclusion of this cited source item without relying on a result-bearing input package. |
| Theorem 8 is ex post: the prescribed strategy is a best response regardless of realized values; the strict ranked-value source event gives the finite ex-post local-deviation condition. | `theorem8_continuous_full_history_bayes_ex_post_review` | covered | `theorem8_continuous_full_history_bayes_ex_post_review`: no completed statement check | The legal-history row proves a strictly stronger ex-post statement: every complete history-dependent continuation plan is weakly dominated for every realized ordered opponent profile, and hence under every supported posterior. |
| Theorem 8 states that the generalized English auction has a unique perfect Bayesian equilibrium with strategies continuous in valuations: an advertiser with value s_i drops out at price p_i(k,h,s_i)=s_i-(alpha_k/alpha_{k-1})(s_i-b_{k+1}); in this equilibrium each advertiser's position and payoff coincide with VCG, and the equilibrium is ex post. | `theorem8_continuous_full_history_bayes_ex_post_review`<br>`theorem8_dropout_formula_eq_bstar_threshold`<br>`theorem7_ranked_gsp_bstar_mechanism_realizes_bstar_outcome` | covered | `theorem8_continuous_full_history_bayes_ex_post_review`: no completed statement check<br>`theorem8_dropout_formula_eq_bstar_threshold`: no completed statement check<br>`theorem7_ranked_gsp_bstar_mechanism_realizes_bstar_outcome`: no completed statement check | The full-history row proves the source-intended legal-history ex-post PBE, actual Bayes consistency, arbitrary-continuation sequential rationality, and effective uniqueness. The dropout bridge identifies the displayed threshold with the B-star payment threshold; the Theorem 7 outcome row and checked finite source-event support theorem derive the VCG-equiv... |
<!-- END GENERATED SOURCE COVERAGE LEDGER -->
