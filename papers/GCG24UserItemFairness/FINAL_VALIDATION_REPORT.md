# Final Validation Report: User-Item Fairness Tradeoffs in Recommendations

Updated: 2026-07-31

## 1. Human Verdict

Formalized. All inventoried source results, including the ten Appendix D/E
targets reopened by semantic review, now have direct source-facing Lean proofs.
Appendix E Lemma 15 contains a documented appendix display/derivation typo;
Lean proves the corrected formula and checks a source-domain counterexample to
the printed display. Independent human review has not been recorded.

## 2. Closeout Status

- Completion status: `formalized`.
- Appendix D Lemmas 4--7 and 10--11 and Appendix E Lemmas 13--15 and 17 now
  expose their complete source conclusions rather than component lemmas.
- The false Lemma 15 center display is quarantined and receives no direct proof
  credit. Its corrected statement and counterexample are separate review rows
  in this post-formalization source-typo note.
- The semantic review resolves every conclusion-bearing dependency on the
  current source and Lean surface. Exact content identities, rather than
  declaration or binder names, control reuse.

## 3. Source and Scope

The source artifact is
`papers/GCG24UserItemFairness/GCG24UserItemFairness.txt`, pinned at SHA-256
`7a0981ed1c26b7e69886e093b37d24b7778a645fe205c301ee14928ddd9c81ea`.
The public source is [OpenReview](https://openreview.net/pdf?id=ZOZjMs3JTs).
The closeout rechecks Proposition 1 at `:292-305`, Theorem 3 at `:368-398`,
Theorem 4 at `:444-470`, Appendix D at `:2170-3180`, and Appendix E at
`:3370-4404`.

The current-protocol source inventory also checks concrete instantiations,
exact or tight conclusions, advertised algorithms, and runtime or complexity
claims. Example 1 and both halves of Theorems 3 and 4 remain mathematical
targets rather than being waived as applications. The paper explicitly
describes its contribution at `:647-649` as conceptual rather than a new
efficient algorithm; its SCS and k-means references are empirical methods, not
named mathematical runtime guarantees.

## 4. Researcher Summary of Checked Results

- D4 constructs the unique Problem 6 optimizer and proves its two-sided
  threshold support from primitive model conditions.
- D5 derives the optimizer value and every displayed `x`/`y` coordinate.
- D6--D7 prove the optimal-policy type-utility order and monotonicity of the
  actual unique optimizer's pivot.
- D10--D11 prove the midpoint pivot bound and optimal item-fairness
  monotonicity on a selected-pivot interval.
- E13 starts from the concrete equality LP's active-basis definition of a
  basic feasible solution and derives the full pivot support pattern.
- E14 constructs and proves uniqueness of the global Problem 11 optimum.
- E15 derives every noncenter coordinate and the corrected center branch for
  an arbitrary global optimum.
- E17 proves right-half zero support for every global optimum without a BFS
  or pivot-support premise.

## 5. Remaining Boundaries and Gaps

There is no open mathematical obligation in the audited GCG24 inventory.
Appendix E Lemma 15 omits one mirrored known-type contribution in the center
item equation. This is a documented appendix typo, not a caveat or Lean proof
boundary. Proposition 2 now states the source's equality-defined type
partition directly, so its conclusion is literal utility-row symmetry rather
than symmetry merely relative to arbitrary declared labels.

## 6. Additional Assumptions Beyond Paper

None. In particular, E13 uses the source's genuine basic-feasible condition:
the concrete Problem 11 equality constraints contain a full active basis. Lean
derives the support-count fact used downstream; it is not a theorem-facing
support certificate or an added assumption. Proposition 2's condition that
equal utility rows determine equal declared types is an explicit source
convention from the paper's definition of the symmetric feasible set, not an
additional assumption introduced by formalization.

## 7. Proof-Strategy Deviations

The source-facing Problem 6 proofs construct a canonical closed policy and
then prove it is the unique optimizer before using its pivot. The Problem 11
proofs derive support and uniqueness internally from mirror symmetry,
item-equality, global optimality, and, only where the source says BFS, a
concrete active basis.

For E15, the formal statement corrects the source rather than adding a premise
that would make the printed equation true.

The paper-interface definitions of normalized item utility, price of fairness,
and price of misestimation use the printed real-division formulas directly.
No extra denominator guard is inserted into the reviewed statement surface;
Lean's real division supplies the ambient total operation while the paper's
positive finite-domain assumptions remain explicit.

## 8. Proof Tricks Worth Reusing

- Prove optimizer existence and uniqueness before exposing closed coordinates.
- Use a concrete active-basis predicate as the BFS primitive and derive sparse
  support from it.
- Separate corrected source statements from checked counterexample rows so a
  false printed claim never receives proof credit.
- Keep midpoint and mirror-index conversions internal to paper-facing rows.

## 9. Generalizations, Conjectures, and Extensions

No stronger generalization is used for source credit. Auxiliary component
lemmas remain available for reuse but are not counted as separate paper
results.

## 10. Mathematical Typos or Other Fixes Suggested in the Source Paper

In Appendix E Lemma 15, the Problem 11 center item equation must retain both
mirrored known-type contributions. At the center, `q_t = 1/2`, so the full
equation gives

`lambda = 1 / (1 + L_t)`.

The printed expression is false. The checked witness `n = 3`, `beta = 2/5`,
`q_t = 1/2`, and `L_t = 4/3` gives corrected value `3/7` and printed value
`9/25`.

### [Appendix E source note](docs/APPENDIX_E_LEMMA15_SOURCE_NOTE.md)

The corrected E15 theorem is formalized. Its false printed center display is
retained as a checked source-typo note because it is confined to an appendix
derivation and does not leave a main-text or downstream theorem obligation
open. A pinned source revision can fix the display, but it is not required for
the paper's `formalized` status.

## 11. Paper Issues or Caveats

None found for the paper-facing mathematical claims. The Appendix E Lemma 15
display noted above is a localized source typo with a checked corrected
statement, not a limitation on the paper's formalization status.

## 12. Detailed Formalization Evidence

The review surface has 49 rows: 38 definitions/results/evidence rows and 11
source-assumption rows. The named-theory source inventory has 26 directly
covered items and one approved corrected target; the Appendix E Lemma 15
printed formula remains quarantined with exact counterexample support.

The current v10 raw source-record receipt covers 34 semantic review rows drawn
from 49 configured review-surface rows, 209 boundary inputs, 20 conclusion
dependencies, 18 recursive fields, and 34 semantic-model records. Its current
judgment summary has 261 judgments, resolves all 20 discovered conclusion
dependencies, and has zero recursion failures. Exact source-semantic and
elaborated-signature pins, rather than declaration names, binder names, or
storage keys, control reuse.

## 13. Paper Assumption Provenance

The 11 configured premise rows are source conditions for the finite fairness
models and optimization problems. The concrete basic-feasible condition in
Appendix E is the source's active-basis condition; sparse support is derived
from it. No additional conclusion-bearing certificate is accepted from the
caller. Premise-level locations are recorded in
`audit/assumption_match_llm.json`.

<!-- BEGIN GENERATED ASSUMPTION PROVENANCE LEDGER -->
### Current Canonical Evidence
Generated from the configured source-condition surface and exact current statement digests in the canonical assumption-provenance sidecar. Model, agent, and automated checks are identified as such; no human review is inferred.

| Assumption declaration | Lean declaration | Source location / statement | Assumption validators | Comments |
| --- | --- | --- | --- | --- |
| Assumption positive recommendation utilities | `assumption_positive_recommendation_utilities` | - The source model uses strictly positive recommendation utilities. This covers Proposition 2's symmetric model and Theorem 3's two opposing-type models. | source condition; Agent check by Codex GCG24 semantic closeout; 2026-07-16 | Source-first semantic review at GCG24UserItemFairness.txt:116-120; GCG24UserItemFairness.txt:368-372. The source model requires strictly positive utilities. The exact premises instantiate that model primitive for the symmetric and opposing-type models used in the cited results. The classification follows the displayed mathematical condition, not the decla... |
| Assumption proposition2 utility rows determine types | `assumption_proposition2_utility_rows_determine_types` | Proposition 2. Ssymm satisfies conditions (i) and (ii) in Proposition 1. Furthermore, solutions ρ ∈ Ssymm to Problem (2) have a sparse structure: • If ρ is a basic feasible solution to the linear program L in Proposition 1, then there are at most n + K − 1 type-item pairs (k, j) such that ρkj > 0 (out of nK possible pairs). • If ρ is also optimal, then there are at most K − 1 items that are ever recommended to more than one type of user, i.e., where ρkj , ρk′ j > 0 for k ̸... | source condition; Agent check by Codex GCG24 semantic closeout; 2026-07-29 | Source-first semantic review at GCG24UserItemFairness.txt:312-316; GCG24UserItemFairness.txt:1889-1890. Proposition 2 defines S_symm by equality of complete utility rows, and Appendix C states that equal utility rows determine the same declared type. Together with the within-type direction in the source model, this is the exact equality-defined partition... |
| Assumption theorem3 opposing type model | `assumption_theorem3_opposing_type_model` | - Theorem 3 compares two instances of the opposing two-type source model with the same positive, strictly decreasing value vector. | source condition; Agent check by Codex GCG24 semantic closeout; 2026-07-16 | Source-first semantic review at GCG24UserItemFairness.txt:368-398; GCG24UserItemFairness.txt:2080-2085. Theorem 3 compares the displayed opposing two-type source models with a common positive, strictly decreasing item-value vector. Every declared type occurring is the population condition needed to represent those displayed source rows from the primitive... |
| Assumption theorem3 first half alpha domain | `assumption_theorem3_first_half_alpha_domain` | - Theorem 3 first-half domain: `alpha` moves toward the balanced population from below. | source condition; Agent check by Codex GCG24 semantic closeout; 2026-07-16 | Source-first semantic review at GCG24UserItemFairness.txt:378-398. Theorem 3's first monotonicity clause explicitly fixes the ordered alpha values in the interval from zero to one half. The classification follows the displayed mathematical condition, not the declaration name. Premise-level checks: 7 result needing review |
| Assumption theorem3 second half alpha domain | `assumption_theorem3_second_half_alpha_domain` | - Theorem 3 second-half domain: `alpha` moves away from the balanced population above `1 / 2`. | source condition; Agent check by Codex GCG24 semantic closeout; 2026-07-16 | Source-first semantic review at GCG24UserItemFairness.txt:378-398. Theorem 3's second monotonicity clause explicitly fixes the ordered alpha values in the interval from one half to one. The classification follows the displayed mathematical condition, not the declaration name. Premise-level checks: 7 result needing review |
| Assumption theorem4 at least three items | `assumption_theorem4_at_least_three_items` | - The Theorem 4 construction uses at least three items. | source condition; Agent check by Codex GCG24 semantic closeout; 2026-07-16 | Source-first semantic review at GCG24UserItemFairness.txt:456-470; GCG24UserItemFairness.txt:3413-3425. Theorem 4's construction is stated for at least three items, which is exactly the integer-domain premise recorded here. The classification follows the displayed mathematical condition, not the declaration name. Premise-level checks: 1 result needing review |
| Assumption theorem4 true model reduction | `assumption_theorem4_true_model_reduction` | - The Theorem 4 true model is the displayed two-type symmetric source model. | source condition; Agent check by Codex GCG24 semantic closeout; 2026-07-16 | Source-first semantic review at GCG24UserItemFairness.txt:444-455; GCG24UserItemFairness.txt:3368-3385. Theorem 4 fixes the true recommendation model to the displayed two-type symmetric source model; the equality is a visible construction condition, not a conclusion package. The classification follows the displayed mathematical condition, not the declarat... |
| Assumption theorem4 estimated model reduction | `assumption_theorem4_estimated_model_reduction` | - The Theorem 4 estimated model is the displayed three-type symmetric source model. | source condition; Agent check by Codex GCG24 semantic closeout; 2026-07-16 | Source-first semantic review at GCG24UserItemFairness.txt:444-455; GCG24UserItemFairness.txt:3368-3385. Theorem 4 fixes the estimated recommendation model to the displayed three-type symmetric source model; the equality is a visible construction condition, not a conclusion package. The classification follows the displayed mathematical condition, not the d... |
| Assumption theorem4 displayed reduced models | `assumption_theorem4_displayed_reduced_models` | - Theorem 4 fixes the true two-type model and the three-type estimated model through the displayed reduced matrices. | source condition; Agent check by Codex GCG24 semantic closeout; 2026-07-16 | Source-first semantic review at GCG24UserItemFairness.txt:444-456; GCG24UserItemFairness.txt:3368-3403. Theorem 4 displays the two-type true and three-type estimated matrices. The type-occurrence conditions and reduced-model identities expose those source data from primitive symmetric models. The classification follows the displayed mathematical condition... |
| Assumption theorem4 cold start type wiring | `assumption_theorem4_cold_start_type_wiring` | - Theorem 4's cold-start row is the estimated third type, whose true type is one of the two opposing source rows. | source condition; Agent check by Codex GCG24 semantic closeout; 2026-07-16 | Source-first semantic review at GCG24UserItemFairness.txt:444-455; GCG24UserItemFairness.txt:498-502. Theorem 4's cold-start construction identifies the estimated third type and its possible true opposing-type rows, while preserving the first two known rows. The classification follows the displayed mathematical condition, not the declaration name. Premise... |
| Assumption theorem4 parameter domain | `assumption_theorem4_parameter_domain` | - Theorem 4 parameter domain for the arbitrary-large misestimation conclusion. | source condition; Agent check by Codex GCG24 semantic closeout; 2026-07-16 | Source-first semantic review at GCG24UserItemFairness.txt:456-470; GCG24UserItemFairness.txt:3340-3354. Theorem 4 explicitly requires positive epsilon and the displayed interval 1/n < beta < 1/2. The classification follows the displayed mathematical condition, not the declaration name. Premise-level checks: 3 result needing review |
<!-- END GENERATED ASSUMPTION PROVENANCE LEDGER -->

## 14. Displayed Formula Provenance

The normalized utilities, fairness prices, optimizer coordinates, pivot
formulas, and corrected Lemma 15 center equation have direct reviewed formula
routes. The false printed center equation is supported only by its
counterexample and receives no proof credit.

<!-- BEGIN GENERATED FORMULA PROVENANCE LEDGER -->
### Current Canonical Evidence
Rows are selected from semantic `formula` and `equation` source-kind metadata within the configured semantic source-coverage scope, never from declaration names. Coverage and statement checks remain separate evidence lanes. Active coverage mode: named theoretical statements.

| Paper formula / subclaim | Lean declaration | Provenance | Validators | Comments |
| --- | --- | --- | --- | --- |
| None | `none` | None | None | No source-map row is canonically classified as a formula or equation. |
<!-- END GENERATED FORMULA PROVENANCE LEDGER -->

## 15. Library Lift Pass

The finite LP, symmetry, and active-basis lemmas are plausible reusable
optimization components. No unresolved reusable-library certificate remains on
the paper-facing theorem routes.

## 16. DAG Audit

`docs/DependencyDAG.tex` records the direct D4--D11 and E13--E17 routes and was
compiled with `latexmk` to `docs/DependencyDAG.pdf`. Lemma 15 is shown as an
ordinary formalized lemma with a corrected-source-typo label. The DAG does not
count the quarantined printed formula as proved.
The rendered PDF was converted to a 120-DPI PNG and visually inspected on
2026-07-16: labels and arrows are readable, no nodes overlap or clip, and the
E15 source-typo label is visually distinct from the formula text it corrects.

## 17. Validation Checks

The focused build and provenance/audit commands are:

```bash
lake build GCG24UserItemFairness
python3 scripts/audit_conclusion_provenance.py --paper GCG24UserItemFairness
python3 scripts/audit_evidence_integrity.py --paper GCG24UserItemFairness
python3 scripts/audit_repository.py --paper GCG24UserItemFairness --paper-closeout --include-active --info-limit 0
python3 scripts/review_dashboard.py --paper GCG24UserItemFairness --precheck
```

The machine audit can establish current source, statement, premise, proof, and
coverage artifacts. Human source-to-Lean signoff remains a separate release
governance step, so the stricter `audit_evidence_integrity.py --release` gate
is not claimed as passing.
<!-- BEGIN GENERATED LLM-AS-JUDGE RESULTS -->
### LLM-as-Judge Results
- Source coverage (`audit/paper_coverage_llm.json`): 26 covered, 1 corrected target covered.
- Statement match (`audit/statement_match_llm.json`): 38 exact match; resolutions: 1 approved corrected source target; source conditions: 11 source condition; diagnostics: 10 orphan/stale statement-sidecar rows excluded.
- Lean-to-TeX translations (`audit/lean_to_tex_llm.json`): 38 row translations generated from Lean statements.
- Assumption provenance (`audit/assumption_match_llm.json`): 11 source condition.
- Source-record classification (`audit/source_record_match_llm.json`): 216 source condition, 3 recursively audited support, 8 non-propositional witness data, 34 semantic model review.
- Source-record structural audit (`audit/source_record_audit.json`): 34 source-record review rows (from 49 configured review-surface rows), 209 boundary inputs, 20 conclusion dependencies, 18 recursive fields, 34 semantic-model records, 0 source-record-only unresolved conclusion dependencies, 0 recursion failures.
- Review-surface audit (`audit/review_surface_llm.json`): review surface passed over 49 review rows.
- Holistic source-first audit (`docs/AGENT_SOURCE_AUDIT.md`): status not inferred by this generator.
- DAG/source/source-json audit (`docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`): status not inferred by this generator.
<!-- END GENERATED LLM-AS-JUDGE RESULTS -->

On 2026-07-29, after the direct Proposition 2 source-facing repair and its
selective semantic reattestation, the focused
`GCG24UserItemFairness.PaperInterface` build completed successfully. The
current conclusion-provenance audit, evidence-integrity audit, review-dashboard
precheck, source-record judgment-summary reconciliation, and paper-closeout
repository audit reported no paper-level semantic or proof findings; the
paper-closeout audit reported zero errors and zero warnings. The current v10
receipt is therefore evidence of the repaired statement surface, rather than a
blanket reuse of a historical aggregate audit identity.

### Current semantic revalidation

Completed on 2026-07-29. Proposition 2 is mapped to its direct
`PaperInterface.lean` theorem, with the source's equality-defined type
partition carried explicitly in the semantic model. The current raw v10 receipt
is pinned at aggregate SHA-256
`a0e1905ff87df2a4ce8009aec752eef7e044e1bc23f075ab2f45e1645762b7b4`.
Its current revalidation and authenticated-evidence composition validate raw,
selected-sidecar, and differential-overlay artifacts before accepting a
descriptor. This is item-level semantic reuse only: names, binders,
declaration spellings, and aggregate freshness alone cannot establish evidence
identity.

## 18. Paper Definitions Checked

The checked definitions include normalized user and item utility, the prices of
fairness and misestimation, the Problem 6 and Problem 11 feasible sets and
objectives, symmetric type partitions, and the concrete basic-feasible
condition used in Appendix E.

## 19. Named Theorem Statements Checked

Proposition 1, Proposition 2, Theorems 3--4, Appendix D Lemmas 4--7 and 10--11,
and Appendix E Lemmas 13--15 and 17 have direct paper-facing endpoints. Lemma
15 uses the corrected center formula described in Section 10.

## 20. Paper-Facing Statement Validator Ledger

The current surface contains 49 reviewed rows. Agent semantic judgments are
current; independent human dashboard review remains 0/49. The complete
declaration-level ledger is stored under `audit/`.

<!-- BEGIN GENERATED STATEMENT VALIDATOR LEDGER -->
### Current Canonical Evidence
Independent human dashboard review: 0/49 rows. No human row-level approval is inferred. review surface passed; Agent check by Codex GCG24 current semantic review-surface reattestation; 2026-07-29 Diagnostic-only evidence excluded from this paper-facing ledger: 10 unconfigured, stale, or ambiguous statement-sidecar rows.

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| - Recommendation utility matrix `w_{ij}` for users and items. | `recommendationUtility` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Agent semantic audit against GCG24UserItemFairness.txt:116-120: compared the source statement, all visible Lean parameters and premises, and the conclusion atom by atom. The judgment is based on the displayed mathematical conditions and source text, not declaration-name similarity. |
| - Raw user utility `sum_j w_ij rho_ij`. | `rawUserUtility` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Agent semantic audit against GCG24UserItemFairness.txt:126-132: compared the source statement, all visible Lean parameters and premises, and the conclusion atom by atom. The judgment is based on the displayed mathematical conditions and source text, not declaration-name similarity. |
| - Normalized user utility `U_i(rho)`. | `normalizedUserUtility` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Agent semantic audit against GCG24UserItemFairness.txt:134-145: compared the source statement, all visible Lean parameters and premises, and the conclusion atom by atom. The judgment is based on the displayed mathematical conditions and source text, not declaration-name similarity. |
| - User fairness objective for a recommendation policy. | `userFairness` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Agent semantic audit against GCG24UserItemFairness.txt:149-150: compared the source statement, all visible Lean parameters and premises, and the conclusion atom by atom. The judgment is based on the displayed mathematical conditions and source text, not declaration-name similarity. |
| - Raw item utility `sum_i w_ij rho_ij`. | `rawItemUtility` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Agent semantic audit against GCG24UserItemFairness.txt:126-132: compared the source statement, all visible Lean parameters and premises, and the conclusion atom by atom. The judgment is based on the displayed mathematical conditions and source text, not declaration-name similarity. |
| - Item normalizer `sum_i w_ij`. | `itemNormalizer` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Agent semantic audit against GCG24UserItemFairness.txt:134-145: compared the source statement, all visible Lean parameters and premises, and the conclusion atom by atom. The judgment is based on the displayed mathematical conditions and source text, not declaration-name similarity. |
| - Normalized item utility `I_j(rho)`. | `normalizedItemUtility` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Agent semantic audit against GCG24UserItemFairness.txt:134-145: compared the source statement, all visible Lean parameters and premises, and the conclusion atom by atom. The judgment is based on the displayed mathematical conditions and source text, not declaration-name similarity. |
| - Item fairness objective for a recommendation policy. | `itemFairness` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Agent semantic audit against GCG24UserItemFairness.txt:149-150: compared the source statement, all visible Lean parameters and premises, and the conclusion atom by atom. The judgment is based on the displayed mathematical conditions and source text, not declaration-name similarity. |
| - Price of fairness at item-fairness level `gamma`. | `priceOfFairnessAt` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Agent semantic audit against GCG24UserItemFairness.txt:172-199: compared the source statement, all visible Lean parameters and premises, and the conclusion atom by atom. The judgment is based on the displayed mathematical conditions and source text, not declaration-name similarity. |
| - Price of maximal item fairness. | `priceOfFairness` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Agent semantic audit against GCG24UserItemFairness.txt:174-199: compared the source statement, all visible Lean parameters and premises, and the conclusion atom by atom. The judgment is based on the displayed mathematical conditions and source text, not declaration-name similarity. |
| - Price of misestimation for a policy selected on an estimated utility matrix. | `priceOfMisestimation` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Agent semantic audit against GCG24UserItemFairness.txt:199-220: compared the source statement, all visible Lean parameters and premises, and the conclusion atom by atom. The judgment is based on the displayed mathematical conditions and source text, not declaration-name similarity. |
| Example 1, diverse-preferences toy instance: recommending each user her favorite item gives maximal normalized user fairness. | `example1_diverse_favorite_policy_user_fairness` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Agent semantic audit against GCG24UserItemFairness.txt:339-343: compared the source statement, all visible Lean parameters and premises, and the conclusion atom by atom. The judgment is based on the displayed mathematical conditions and source text, not declaration-name similarity. |
| Example 1, diverse-preferences toy instance: the same favorite-item policy equalizes item utility at the displayed 10/11 normalized value. | `example1_diverse_favorite_policy_item_fairness` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Agent semantic audit against GCG24UserItemFairness.txt:339-343: compared the source statement, all visible Lean parameters and premises, and the conclusion atom by atom. The judgment is based on the displayed mathematical conditions and source text, not declaration-name similarity. |
| Example 1, homogeneous-preferences algebra: the displayed bounds imply the linear normalized user/item fairness tradeoff Umin + Imin <= 1 + epsilon. | `example1_homogeneous_tradeoff_bound` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Agent semantic audit against GCG24UserItemFairness.txt:344-364: compared the source statement, all visible Lean parameters and premises, and the conclusion atom by atom. The judgment is based on the displayed mathematical conditions and source text, not declaration-name similarity. |
| Appendix C, Lemma 1: the optimal item-fairness value is positive. | `appendix_c_lemma1_item_fairness_positive` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Source-first revalidation against GCG24UserItemFairness.txt:1742-1746: inspected the printed statement and current elaborated Lean declaration atom by atom. The visible model data, hypotheses, and result agree without a caller-supplied result component. |
| Appendix C, Lemma 2: under the positive utility model, a policy solves the original max-min item-fairness problem exactly when it is the policy component of an optimizer of the equality-form LP imposing I_j(rho) = ell for every item. | `appendix_c_lemma2_item_fairness_equality_lp_solution_set` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Source-first review at GCG24UserItemFairness.txt:1759-1800: the strengthened PaperInterface theorem now retains the source optimizer-set equivalence, rather than only equality of LP values. It explicitly includes the equality-form LP feasible policy/level witness and the global level-maximality condition. |
| Appendix D, Lemma 3: unconstrained user-fairness baseline. | `appendix_d_lemma3_unconstrained_baseline` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Source-first revalidation against GCG24UserItemFairness.txt:2098-2110; GCG24UserItemFairness.txt:2381-2415: inspected the printed statement and current elaborated Lean declaration atom by atom. The visible model data, hypotheses, and result agree without a caller-supplied result component. |
| Appendix D, Lemma 4: Problem 6 has a unique solution (x, y, lambda), with a threshold t such that x_j = 0 above t and y_j = 0 below t. | `appendix_d_lemma4_problem6_unique_sparse_solution` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Source-first review at GCG24UserItemFairness.txt:2183-2185; GCG24UserItemFairness.txt:2417-2645 expanded the named model vocabulary and checked every elaborated parameter, premise, and conclusion atom. The conclusion contains existence, global optimality, both threshold-support directions, and uniqueness; no support or uniqueness conclusion is supplied as... |
| Appendix D, Lemma 5: at the active pivot t(alpha), the unique Problem 6 solution has the displayed lambda, x_j, and y_j closed forms. | `appendix_d_lemma5_problem6_active_optimizer_closed_form` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Source-first review at GCG24UserItemFairness.txt:2190-2256; GCG24UserItemFairness.txt:2641-2835 expanded the named model vocabulary and checked every elaborated parameter, premise, and conclusion atom. The theorem derives the optimizer, uniqueness, active pivot, objective value, and every displayed coordinate formula from the source model primitives. |
| Appendix D, Lemma 6: for 0 < alpha < 1/2, type-1 users have weakly larger utility than type-2 users under the optimal recommendation policy. | `appendix_d_lemma6_optimal_policy_type_utility_order` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Source-first review at GCG24UserItemFairness.txt:2257-2260; GCG24UserItemFairness.txt:2828-2962 expanded the named model vocabulary and checked every elaborated parameter, premise, and conclusion atom. Lean indexes the source's first user type by 0 and second by 1, so its inequality is exactly the printed type-1-versus-type-2 utility ordering. |
| Appendix D, Lemma 7: the pivot t(alpha) of the unique Problem 6 optimizer is weakly increasing in alpha. | `appendix_d_lemma7_active_optimizer_pivot_monotonicity` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Source-first review at GCG24UserItemFairness.txt:2315-2315; GCG24UserItemFairness.txt:2963-3064 expanded the named model vocabulary and checked every elaborated parameter, premise, and conclusion atom. The two canonical policies denote the unique optimizers proved by the preceding source-facing lemmas, so their last-active indices are the source pivots t(... |
| Appendix D, Lemma 8: optimal item fairness I_min^*(alpha) is increasing on 0 < alpha <= 1/2. | `appendix_d_lemma8_selected_pivot_stitching` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Source-first revalidation against GCG24UserItemFairness.txt:2317-2318; GCG24UserItemFairness.txt:3066-3098: inspected the printed statement and current elaborated Lean declaration atom by atom. The visible model data, hypotheses, and result agree without a caller-supplied result component. |
| Appendix D, Lemma 9: q_j(alpha) strictly increases in alpha and strictly decreases in the item index j. | `appendix_d_lemma9_pair_share_algebra` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Source-first revalidation against GCG24UserItemFairness.txt:2320-2320; GCG24UserItemFairness.txt:2340-2380: inspected the printed statement and current elaborated Lean declaration atom by atom. The visible model data, hypotheses, and result agree without a caller-supplied result component. |
| Appendix D, Lemma 10: for alpha <= 1/2, the pivot t(alpha) of the unique Problem 6 optimizer is at most the midpoint (n + 1) / 2. | `appendix_d_lemma10_active_optimizer_pivot_at_or_before_midpoint` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Source-first review at GCG24UserItemFairness.txt:3071-3077; GCG24UserItemFairness.txt:3101-3150 expanded the named model vocabulary and checked every elaborated parameter, premise, and conclusion atom. The reverse-index inequality is the zero-based finite-index form of the source bound t(alpha) <= (n+1)/2. |
| Appendix D, Lemma 11: optimal item fairness is increasing on each selected-pivot interval A(t) with t at or before the midpoint. | `appendix_d_lemma11_optimal_item_fairness_mono_on_active_pivot_interval` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Source-first review at GCG24UserItemFairness.txt:3079-3098; GCG24UserItemFairness.txt:3151-3180 expanded the named model vocabulary and checked every elaborated parameter, premise, and conclusion atom. The equal-pivot premise is exactly membership in one selected-pivot interval A(t), and the midpoint premise is the source restriction on that interval. |
| Appendix E, Lemma 12: symmetrized estimated policy optimality. | `appendix_e_lemma12_symmetrized_policy` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Source-first revalidation against GCG24UserItemFairness.txt:3379-3385; GCG24UserItemFairness.txt:3739-3832: inspected the printed statement and current elaborated Lean declaration atom by atom. The visible model data, hypotheses, and result agree without a caller-supplied result component. |
| Appendix E, Lemma 13: every optimal basic feasible Problem 11 solution has a midpoint-or-earlier pivot t with x_j = 0 above t and z_j = z_rev(j) = 0 below t. | `appendix_e_lemma13_every_optimal_basic_solution_has_pivot_support` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Source-first review at GCG24UserItemFairness.txt:3403-3411; GCG24UserItemFairness.txt:3833-3844 expanded the named model vocabulary and checked every elaborated parameter, premise, and conclusion atom. The visible IsEqualityLPBasicFeasible premise is the source lemma's genuine basic-feasible-solution qualifier: it requires a full active basis for the conc... |
| Appendix E, Lemma 14: Problem 11 has a unique optimal solution. | `appendix_e_lemma14_problem11_has_unique_optimal_solution` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Source-first review at GCG24UserItemFairness.txt:3413-3413; GCG24UserItemFairness.txt:4153-4238 expanded the named model vocabulary and checked every elaborated parameter, premise, and conclusion atom. The conclusion constructs an optimum and quantifies over every other global optimum to state policy and value uniqueness; no optimizer certificate is an in... |
| Appendix E, Lemma 15 corrected target: for the equality-form LP solved in the lemma, the printed noncenter lambda, x, and z coordinate formulas hold; at the center pivot z_t = 1 and lambda = 1 / (1 + L_t). | `appendix_e_lemma15_optimal_solution_full_closed_form` | exact match; approved corrected source target; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Source-first review of the approved Appendix E Lemma 15 corrected target: the equality-form LP endpoint includes the printed noncenter formulas and, at the center pivot, z_t = 1 and lambda = 1/(1 + L_t). The archival mirror-center formula is retained only as a documented source typo. The archival printed center formula is not credited. This row reviews on... |
| Checked Appendix E Lemma 15 defect witness: n = 3, beta = 2/5, q_t = 1/2, and L_t = 4/3 satisfy the source parameter range, but the corrected full-equation center value 1 / (1 + L_t) differs from the printed center formula. | `appendix_e_lemma15_printed_center_value_counterexample` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Source-first review at GCG24UserItemFairness.txt:3899-3924; GCG24UserItemFairness.txt:4290-4332 expanded the named model vocabulary and checked every elaborated parameter, premise, and conclusion atom. This is a checked arithmetic witness to the recorded source defect: the corrected value is 3/7 and the printed value is 9/25. |
| Appendix E, Lemma 16: q_j(1/2) is above, below, or equal to 1/2 according as j is before, after, or at the item midpoint. | `appendix_e_lemma16_midpoint_order_algebra` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Source-first revalidation against GCG24UserItemFairness.txt:3713-3735: inspected the printed statement and current elaborated Lean declaration atom by atom. The visible model data, hypotheses, and result agree without a caller-supplied result component. |
| Appendix E, Lemma 17: for every optimal Problem 11 solution, x_j = 0 for items j after the midpoint. | `appendix_e_lemma17_every_optimal_solution_has_no_right_half_support` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Source-first review at GCG24UserItemFairness.txt:3845-3868; GCG24UserItemFairness.txt:4108-4152 expanded the named model vocabulary and checked every elaborated parameter, premise, and conclusion atom. The policy is arbitrary among all global Problem 11 optima, and no basic-feasibility or pivot-support certificate is assumed. |
| Proposition 1. Let S be a set of recommendation policies described by finitely many linear constraints. If an optimal Problem-(2) policy rho* belongs to S and is the unique maximal-item-fairness-feasible policy in S, then rho* is recovered as the unique policy optimizer of the equality-form linear program L obtained by adding S to the constraints I_j(rho) = lambda for every item. | `proposition1_symmetric_lp_reduction` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Agent semantic audit against GCG24UserItemFairness.txt:292-305; GCG24UserItemFairness.txt:1751-1800: compared the source statement, all visible Lean parameters and premises, and the conclusion atom by atom. The judgment is based on the displayed mathematical conditions and source text, not declaration-name similarity. |
| Proposition 2. The source policy set S_symm = {rho : rho_i = rho_i' whenever w_i = w_i'} satisfies Proposition 1 conditions (i) and (ii). Under the source's equality-defined type convention, if a type-level policy is a basic feasible solution of L, at most n + K - 1 type-item coordinates are positive; if it is also optimal, at most K - 1 items are recommended with positive probability to more than one type. | `proposition2_symmetric_optimum_exists` | exact match; Agent check by Codex GCG24 Proposition 2 current semantic reattestation; 2026-07-29. Lean translation recorded; Agent check by Codex GCG24 Proposition 2 current source-facing reattestation; 2026-07-29 | Independent current semantic audit against the source Proposition 2 statement and Appendix C equality convention: the reviewed Lean type exposes the literal utility-row symmetry set, the two-way equality-defined type convention as a visible source premise, the finite equality characterization, the optimal symmetric-policy witness, and both conditional spa... |
| - Theorem 3, first half: in the opposing two-type model, increasing `alpha` toward `1 / 2` weakly decreases the price of fairness. | `theorem3_price_decreases_first_half` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Agent semantic audit against GCG24UserItemFairness.txt:391-398; GCG24UserItemFairness.txt:2078-2185: compared the source statement, all visible Lean parameters and premises, and the conclusion atom by atom. The judgment is based on the displayed mathematical conditions and source text, not declaration-name similarity. |
| - Theorem 3, second half: in the opposing two-type model, increasing `alpha` away from `1 / 2` weakly increases the price of fairness. | `theorem3_price_increases_second_half` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Agent semantic audit against GCG24UserItemFairness.txt:391-398; GCG24UserItemFairness.txt:2078-2185: compared the source statement, all visible Lean parameters and premises, and the conclusion atom by atom. The judgment is based on the displayed mathematical conditions and source text, not declaration-name similarity. |
| - Theorem 4 final tradeoff, cold-start user whose true row is the first opposing type: without fairness the misestimation price is at most `1/2`, while with maximal item fairness some estimated optimum has misestimation price above `1 - eps`. | `theorem4_misestimation_tradeoff_typeZero` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Agent semantic audit against GCG24UserItemFairness.txt:456-470; GCG24UserItemFairness.txt:3338-3705: compared the source statement, all visible Lean parameters and premises, and the conclusion atom by atom. The judgment is based on the displayed mathematical conditions and source text, not declaration-name similarity. |
| - Theorem 4 final tradeoff for the second opposing true type. | `theorem4_misestimation_tradeoff_typeOne` | exact match; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27. Lean translation recorded; Agent check by Codex GCG24 source-first v10 closeout audit; 2026-07-27 | Agent semantic audit against GCG24UserItemFairness.txt:456-470; GCG24UserItemFairness.txt:3338-3705: compared the source statement, all visible Lean parameters and premises, and the conclusion atom by atom. The judgment is based on the displayed mathematical conditions and source text, not declaration-name similarity. |
| - The source model uses strictly positive recommendation utilities. This covers Proposition 2's symmetric model and Theorem 3's two opposing-type models. | `assumption_positive_recommendation_utilities` | source condition; Agent check by Codex GCG24 semantic closeout; 2026-07-16 | Source-first semantic review at GCG24UserItemFairness.txt:116-120; GCG24UserItemFairness.txt:368-372. The source model requires strictly positive utilities. The exact premises instantiate that model primitive for the symmetric and opposing-type models used in the cited results. The classification follows the displayed mathematical condition, not the decla... |
| Proposition 2. Ssymm satisfies conditions (i) and (ii) in Proposition 1. Furthermore, solutions ρ ∈ Ssymm to Problem (2) have a sparse structure: • If ρ is a basic feasible solution to the linear program L in Proposition 1, then there are at most n + K − 1 type-item pairs (k, j) such that ρkj > 0 (out of nK possible pairs). • If ρ is also optimal, then there are at most K − 1 items that are ever recommended to mor... | `assumption_proposition2_utility_rows_determine_types` | source condition; Agent check by Codex GCG24 semantic closeout; 2026-07-29 | Source-first semantic review at GCG24UserItemFairness.txt:312-316; GCG24UserItemFairness.txt:1889-1890. Proposition 2 defines S_symm by equality of complete utility rows, and Appendix C states that equal utility rows determine the same declared type. Together with the within-type direction in the source model, this is the exact equality-defined partition... |
| - Theorem 3 compares two instances of the opposing two-type source model with the same positive, strictly decreasing value vector. | `assumption_theorem3_opposing_type_model` | source condition; Agent check by Codex GCG24 semantic closeout; 2026-07-16 | Source-first semantic review at GCG24UserItemFairness.txt:368-398; GCG24UserItemFairness.txt:2080-2085. Theorem 3 compares the displayed opposing two-type source models with a common positive, strictly decreasing item-value vector. Every declared type occurring is the population condition needed to represent those displayed source rows from the primitive... |
| - Theorem 3 first-half domain: `alpha` moves toward the balanced population from below. | `assumption_theorem3_first_half_alpha_domain` | source condition; Agent check by Codex GCG24 semantic closeout; 2026-07-16 | Source-first semantic review at GCG24UserItemFairness.txt:378-398. Theorem 3's first monotonicity clause explicitly fixes the ordered alpha values in the interval from zero to one half. The classification follows the displayed mathematical condition, not the declaration name. |
| - Theorem 3 second-half domain: `alpha` moves away from the balanced population above `1 / 2`. | `assumption_theorem3_second_half_alpha_domain` | source condition; Agent check by Codex GCG24 semantic closeout; 2026-07-16 | Source-first semantic review at GCG24UserItemFairness.txt:378-398. Theorem 3's second monotonicity clause explicitly fixes the ordered alpha values in the interval from one half to one. The classification follows the displayed mathematical condition, not the declaration name. |
| - The Theorem 4 construction uses at least three items. | `assumption_theorem4_at_least_three_items` | source condition; Agent check by Codex GCG24 semantic closeout; 2026-07-16 | Source-first semantic review at GCG24UserItemFairness.txt:456-470; GCG24UserItemFairness.txt:3413-3425. Theorem 4's construction is stated for at least three items, which is exactly the integer-domain premise recorded here. The classification follows the displayed mathematical condition, not the declaration name. |
| - The Theorem 4 true model is the displayed two-type symmetric source model. | `assumption_theorem4_true_model_reduction` | source condition; Agent check by Codex GCG24 semantic closeout; 2026-07-16 | Source-first semantic review at GCG24UserItemFairness.txt:444-455; GCG24UserItemFairness.txt:3368-3385. Theorem 4 fixes the true recommendation model to the displayed two-type symmetric source model; the equality is a visible construction condition, not a conclusion package. The classification follows the displayed mathematical condition, not the declarat... |
| - The Theorem 4 estimated model is the displayed three-type symmetric source model. | `assumption_theorem4_estimated_model_reduction` | source condition; Agent check by Codex GCG24 semantic closeout; 2026-07-16 | Source-first semantic review at GCG24UserItemFairness.txt:444-455; GCG24UserItemFairness.txt:3368-3385. Theorem 4 fixes the estimated recommendation model to the displayed three-type symmetric source model; the equality is a visible construction condition, not a conclusion package. The classification follows the displayed mathematical condition, not the d... |
| - Theorem 4 fixes the true two-type model and the three-type estimated model through the displayed reduced matrices. | `assumption_theorem4_displayed_reduced_models` | source condition; Agent check by Codex GCG24 semantic closeout; 2026-07-16 | Source-first semantic review at GCG24UserItemFairness.txt:444-456; GCG24UserItemFairness.txt:3368-3403. Theorem 4 displays the two-type true and three-type estimated matrices. The type-occurrence conditions and reduced-model identities expose those source data from primitive symmetric models. The classification follows the displayed mathematical condition... |
| - Theorem 4's cold-start row is the estimated third type, whose true type is one of the two opposing source rows. | `assumption_theorem4_cold_start_type_wiring` | source condition; Agent check by Codex GCG24 semantic closeout; 2026-07-16 | Source-first semantic review at GCG24UserItemFairness.txt:444-455; GCG24UserItemFairness.txt:498-502. Theorem 4's cold-start construction identifies the estimated third type and its possible true opposing-type rows, while preserving the first two known rows. The classification follows the displayed mathematical condition, not the declaration name. |
| - Theorem 4 parameter domain for the arbitrary-large misestimation conclusion. | `assumption_theorem4_parameter_domain` | source condition; Agent check by Codex GCG24 semantic closeout; 2026-07-16 | Source-first semantic review at GCG24UserItemFairness.txt:456-470; GCG24UserItemFairness.txt:3340-3354. Theorem 4 explicitly requires positive epsilon and the displayed interval 1/n < beta < 1/2. The classification follows the displayed mathematical condition, not the declaration name. |
<!-- END GENERATED STATEMENT VALIDATOR LEDGER -->

## 21. Source-Coverage Audit Ledger

The normal named-theory ledger contains 27 selected results: 26 are covered
directly and Appendix E Lemma 15 is covered on its explicitly corrected target.
The larger source map also records model, formula, and refutation support so
those components cannot be mistaken for independent theorem proofs.

<!-- BEGIN GENERATED SOURCE COVERAGE LEDGER -->
### Current Canonical Evidence
- Coverage scope: named theoretical statements.
- Source inventory: 27 source statements from `GCG24UserItemFairness.txt`.
- Coverage result: 1 corrected target covered, 26 covered.
- Coverage review: coverage ledger recorded; Agent check by Codex GCG24 source-first v10 selective closeout audit; 2026-07-29.
- Row-local statement checks: 23/27 linked row references have a completed canonical statement check; repeated links are counted per source row.

| Source statement | Linked Lean review rows | Coverage judgment | Row-local statement checks | Comments |
| --- | --- | --- | --- | --- |
| Proposition 1. Let S be a set of recommendation policies described by finitely many linear constraints. If an optimal Problem-(2) policy rho* belongs to S and is the unique maximal-item-fairness-feasible policy in S, then rho* is recovered as the unique policy optimizer of the equality-form linear program L obtained by adding S to the constraints I_j(rho) = lambda for every item. | `proposition1_symmetric_lp_reduction` | covered | `proposition1_symmetric_lp_reduction`: exact match | The cited row has a current atom-by-atom semantic ledger that binds the source statement's displayed inputs and conclusion to the current elaborated PaperInterface type; this route is established by source text and signature pins, not by declaration naming. |
| Proposition 2. The source policy set S_symm = {rho : rho_i = rho_i' whenever w_i = w_i'} satisfies Proposition 1 conditions (i) and (ii). Under the source's equality-defined type convention, if a type-level policy is a basic feasible solution of L, at most n + K - 1 type-item coordinates are positive; if it is also optimal, at most K - 1 items are recommended with positive probability to more than one type. | `proposition2_symmetric_optimum_exists` | covered | `proposition2_symmetric_optimum_exists`: exact match | The cited row has a current atom-by-atom semantic ledger binding the source equality-of-utility-rows policy set, its explicit two-way type convention, and every displayed sparse-policy conclusion to the current elaborated PaperInterface type. This route is established by source text and semantic/signature pins, not by declaration naming. |
| Appendix C, Lemma 1: the optimal item-fairness value is positive. | `appendix_c_lemma1_item_fairness_positive` | covered | `appendix_c_lemma1_item_fairness_positive`: exact match | The cited row has a current atom-by-atom semantic ledger that binds the source statement's displayed inputs and conclusion to the current elaborated PaperInterface type; this route is established by source text and signature pins, not by declaration naming. |
| Appendix D, Lemma 10: for alpha <= 1/2, the pivot t(alpha) of the unique Problem 6 optimizer is at most the midpoint (n + 1) / 2. | `appendix_d_lemma10_active_optimizer_pivot_at_or_before_midpoint` | covered | `appendix_d_lemma10_active_optimizer_pivot_at_or_before_midpoint`: exact match | The cited row has a current atom-by-atom semantic ledger that binds the source statement's displayed inputs and conclusion to the current elaborated PaperInterface type; this route is established by source text and signature pins, not by declaration naming. |
| Appendix D, Lemma 11: optimal item fairness is increasing on each selected-pivot interval A(t) with t at or before the midpoint. | `appendix_d_lemma11_optimal_item_fairness_mono_on_active_pivot_interval` | covered | `appendix_d_lemma11_optimal_item_fairness_mono_on_active_pivot_interval`: exact match | The cited row has a current atom-by-atom semantic ledger that binds the source statement's displayed inputs and conclusion to the current elaborated PaperInterface type; this route is established by source text and signature pins, not by declaration naming. |
| Appendix D, Lemma 3: unconstrained user-fairness baseline. | `appendix_d_lemma3_unconstrained_baseline` | covered | `appendix_d_lemma3_unconstrained_baseline`: exact match | The cited row has a current atom-by-atom semantic ledger that binds the source statement's displayed inputs and conclusion to the current elaborated PaperInterface type; this route is established by source text and signature pins, not by declaration naming. |
| Appendix D, Lemma 4: Problem 6 has a unique solution (x, y, lambda), with a threshold t such that x_j = 0 above t and y_j = 0 below t. | `appendix_d_lemma4_problem6_unique_sparse_solution` | covered | `appendix_d_lemma4_problem6_unique_sparse_solution`: exact match | The cited row has a current atom-by-atom semantic ledger that binds the source statement's displayed inputs and conclusion to the current elaborated PaperInterface type; this route is established by source text and signature pins, not by declaration naming. |
| Appendix D, Lemma 5: at the active pivot t(alpha), the unique Problem 6 solution has the displayed lambda, x_j, and y_j closed forms. | `appendix_d_lemma5_problem6_active_optimizer_closed_form` | covered | `appendix_d_lemma5_problem6_active_optimizer_closed_form`: exact match | The cited row has a current atom-by-atom semantic ledger that binds the source statement's displayed inputs and conclusion to the current elaborated PaperInterface type; this route is established by source text and signature pins, not by declaration naming. |
| Appendix D, Lemma 6: for 0 < alpha < 1/2, type-1 users have weakly larger utility than type-2 users under the optimal recommendation policy. | `appendix_d_lemma6_optimal_policy_type_utility_order` | covered | `appendix_d_lemma6_optimal_policy_type_utility_order`: exact match | The cited row has a current atom-by-atom semantic ledger that binds the source statement's displayed inputs and conclusion to the current elaborated PaperInterface type; this route is established by source text and signature pins, not by declaration naming. |
| Appendix D, Lemma 7: the pivot t(alpha) of the unique Problem 6 optimizer is weakly increasing in alpha. | `appendix_d_lemma7_active_optimizer_pivot_monotonicity` | covered | `appendix_d_lemma7_active_optimizer_pivot_monotonicity`: exact match | The cited row has a current atom-by-atom semantic ledger that binds the source statement's displayed inputs and conclusion to the current elaborated PaperInterface type; this route is established by source text and signature pins, not by declaration naming. |
| Appendix D, Lemma 8: optimal item fairness I_min^*(alpha) is increasing on 0 < alpha <= 1/2. | `appendix_d_lemma8_selected_pivot_stitching` | covered | `appendix_d_lemma8_selected_pivot_stitching`: exact match | The cited row has a current atom-by-atom semantic ledger that binds the source statement's displayed inputs and conclusion to the current elaborated PaperInterface type; this route is established by source text and signature pins, not by declaration naming. |
| Appendix D, Lemma 9: q_j(alpha) strictly increases in alpha and strictly decreases in the item index j. | `appendix_d_lemma9_pair_share_algebra` | covered | `appendix_d_lemma9_pair_share_algebra`: exact match | The cited row has a current atom-by-atom semantic ledger that binds the source statement's displayed inputs and conclusion to the current elaborated PaperInterface type; this route is established by source text and signature pins, not by declaration naming. |
| Appendix E, Lemma 12: symmetrized estimated policy optimality. | `appendix_e_lemma12_symmetrized_policy` | covered | `appendix_e_lemma12_symmetrized_policy`: exact match | The cited row has a current atom-by-atom semantic ledger that binds the source statement's displayed inputs and conclusion to the current elaborated PaperInterface type; this route is established by source text and signature pins, not by declaration naming. |
| Appendix E, Lemma 13: every optimal basic feasible Problem 11 solution has a midpoint-or-earlier pivot t with x_j = 0 above t and z_j = z_rev(j) = 0 below t. | `appendix_e_lemma13_every_optimal_basic_solution_has_pivot_support` | covered | `appendix_e_lemma13_every_optimal_basic_solution_has_pivot_support`: exact match | The cited row has a current atom-by-atom semantic ledger that binds the source statement's displayed inputs and conclusion to the current elaborated PaperInterface type; this route is established by source text and signature pins, not by declaration naming. |
| Appendix E, Lemma 14: Problem 11 has a unique optimal solution. | `appendix_e_lemma14_problem11_has_unique_optimal_solution` | covered | `appendix_e_lemma14_problem11_has_unique_optimal_solution`: exact match | The cited row has a current atom-by-atom semantic ledger that binds the source statement's displayed inputs and conclusion to the current elaborated PaperInterface type; this route is established by source text and signature pins, not by declaration naming. |
| Appendix E, Lemma 15 (archival printed statement): for the unique optimal Problem 12 solution, the displayed noncenter lambda, x, and z formulas hold; at the center pivot it prints z_t = 1 and lambda = (2 beta q_t + (1 - 2 beta)) / (1 + q_t L_t). | `appendix_e_lemma15_optimal_solution_full_closed_form` | corrected target covered | `appendix_e_lemma15_optimal_solution_full_closed_form`: exact match; approved corrected source target | The cited row has a current atom-by-atom semantic ledger that binds the source statement's displayed inputs and conclusion to the current elaborated PaperInterface type; this route is established by source text and signature pins, not by declaration naming. |
| Appendix E, Lemma 16: q_j(1/2) is above, below, or equal to 1/2 according as j is before, after, or at the item midpoint. | `appendix_e_lemma16_midpoint_order_algebra` | covered | `appendix_e_lemma16_midpoint_order_algebra`: exact match | The cited row has a current atom-by-atom semantic ledger that binds the source statement's displayed inputs and conclusion to the current elaborated PaperInterface type; this route is established by source text and signature pins, not by declaration naming. |
| Appendix E, Lemma 17: for every optimal Problem 11 solution, x_j = 0 for items j after the midpoint. | `appendix_e_lemma17_every_optimal_solution_has_no_right_half_support` | covered | `appendix_e_lemma17_every_optimal_solution_has_no_right_half_support`: exact match | The cited row has a current atom-by-atom semantic ledger that binds the source statement's displayed inputs and conclusion to the current elaborated PaperInterface type; this route is established by source text and signature pins, not by declaration naming. |
| - Theorem 3, first half: in the opposing two-type model, increasing `alpha` toward `1 / 2` weakly decreases the price of fairness. | `theorem3_price_decreases_first_half` | covered | `theorem3_price_decreases_first_half`: exact match | The cited row has a current atom-by-atom semantic ledger that binds the source statement's displayed inputs and conclusion to the current elaborated PaperInterface type; this route is established by source text and signature pins, not by declaration naming. |
| - Theorem 3, second half: in the opposing two-type model, increasing `alpha` away from `1 / 2` weakly increases the price of fairness. | `theorem3_price_increases_second_half` | covered | `theorem3_price_increases_second_half`: exact match | The cited row has a current atom-by-atom semantic ledger that binds the source statement's displayed inputs and conclusion to the current elaborated PaperInterface type; this route is established by source text and signature pins, not by declaration naming. |
| - Theorem 4 final tradeoff for the second opposing true type. | `theorem4_misestimation_tradeoff_typeOne` | covered | `theorem4_misestimation_tradeoff_typeOne`: exact match | The cited row has a current atom-by-atom semantic ledger that binds the source statement's displayed inputs and conclusion to the current elaborated PaperInterface type; this route is established by source text and signature pins, not by declaration naming. |
| - Theorem 4 final tradeoff, cold-start user whose true row is the first opposing type: without fairness the misestimation price is at most `1/2`, while with maximal item fairness some estimated optimum has misestimation price above `1 - eps`. | `theorem4_misestimation_tradeoff_typeZero` | covered | `theorem4_misestimation_tradeoff_typeZero`: exact match | The cited row has a current atom-by-atom semantic ledger that binds the source statement's displayed inputs and conclusion to the current elaborated PaperInterface type; this route is established by source text and signature pins, not by declaration naming. |
| Appendix C, Lemma 2: under the positive utility model, a policy solves the original max-min item-fairness problem exactly when it is the policy component of an optimizer of the equality-form LP imposing I_j(rho) = ell for every item. | `appendix_c_lemma2_item_fairness_equality_lp_solution_set` | covered | `appendix_c_lemma2_item_fairness_equality_lp_solution_set`: exact match | The cited row has a current atom-by-atom semantic ledger that binds the source statement's displayed inputs and conclusion to the current elaborated PaperInterface type; this route is established by source text and signature pins, not by declaration naming. |
| - Theorem 3 first-half domain: `alpha` moves toward the balanced population from below. | `assumption_theorem3_first_half_alpha_domain` | covered | `assumption_theorem3_first_half_alpha_domain`: no completed statement check | The cited row has a current atom-by-atom semantic ledger that binds the source statement's displayed inputs and conclusion to the current elaborated PaperInterface type; this route is established by source text and signature pins, not by declaration naming. |
| - Theorem 3 compares two instances of the opposing two-type source model with the same positive, strictly decreasing value vector. | `assumption_theorem3_opposing_type_model` | covered | `assumption_theorem3_opposing_type_model`: no completed statement check | The cited row has a current atom-by-atom semantic ledger that binds the source statement's displayed inputs and conclusion to the current elaborated PaperInterface type; this route is established by source text and signature pins, not by declaration naming. |
| - Theorem 3 second-half domain: `alpha` moves away from the balanced population above `1 / 2`. | `assumption_theorem3_second_half_alpha_domain` | covered | `assumption_theorem3_second_half_alpha_domain`: no completed statement check | The cited row has a current atom-by-atom semantic ledger that binds the source statement's displayed inputs and conclusion to the current elaborated PaperInterface type; this route is established by source text and signature pins, not by declaration naming. |
| - Theorem 4 fixes the true two-type model and the three-type estimated model through the displayed reduced matrices. | `assumption_theorem4_displayed_reduced_models` | covered | `assumption_theorem4_displayed_reduced_models`: no completed statement check | The cited row has a current atom-by-atom semantic ledger that binds the source statement's displayed inputs and conclusion to the current elaborated PaperInterface type; this route is established by source text and signature pins, not by declaration naming. |
<!-- END GENERATED SOURCE COVERAGE LEDGER -->
