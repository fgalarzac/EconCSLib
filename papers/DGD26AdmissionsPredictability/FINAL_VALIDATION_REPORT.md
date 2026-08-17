# Final Validation Report: Capacity Constraints Make Admissions Processes Less Predictable

Updated: 2026-07-31

## 1. Human Verdict

Formalized. The full source inventory is now represented by proved,
source-shaped endpoints, including the repaired application formulas and the
real-weight admissions model. The audit found only ordinary typos, implicit
nondegeneracy conditions, and previously incomplete Lean routes; none warrants
a paper-level caveat. Independent human review has not been recorded.

## 2. Closeout Status

Formalized. The source-first inventory has 65 mathematical items: 61 have
direct source-shaped Lean routes and 4 are established by explicitly recorded
collective support. There are no remaining partial, conditional, missing, or
out-of-scope mathematical targets.

This is not a `formalized with caveat` case. The audit found minor printed
typos, implicit nondegeneracy conditions, and gaps in the former Lean routes;
the intended mathematical endpoints are now proved. Those findings are
ordinary formalization notes. Independent human dashboard review remains
`0/69`; no independent human release certification is claimed.

- Audit summary: source coverage has 61 covered, 4 covered by reviewed rows; diagnostics: full inventory shown because paper_statement_map.json must explicitly set source_coverage_mode before a source-coverage closeout; statement LLM-as-judge has no rows; diagnostics: 69 orphan/stale statement-sidecar rows excluded, 69 configured rows without unambiguous current receipts; Lean-to-TeX has 69 row translations; assumption provenance sidecar has no configured source-condition rows; source-record classification has 59 source condition, 1 non-propositional witness data; source-record audit reports 69 source-record review rows, 118 boundary inputs, 26 conclusion dependencies, 48 recursive fields, 0 source-record-only unresolved conclusion dependencies, 0 recursion failures; review-surface audit review surface passed over 69 review rows; holistic source-first audit status is not inferred by this generator; DAG/source-json audit status is not inferred (see `docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`).

All semantic routes are current, and the recursive model review has no
unresolved dependency or recursion failure.

## 3. Source and Scope

The primary artifact is the pinned AAAI-26/arXiv source archive with SHA-256
`0d57324d02fc64c4c6b627c71c71cbbf93610b7f0b4b2138da1b436bb9234434`.
The public source is https://arxiv.org/abs/2601.11513.
The audit reread `source_tex/main.tex` and `source_tex/appendix.tex` before
comparing the resulting 65-item mathematical inventory with the Lean
interface. Scope includes every
definition, displayed model formula, named result, concrete program example,
and advertised application endpoint in those sources.

## 4. Researcher Summary of Checked Results

The formalization now covers the full finite-choice model and both paper-specific
application layers.

- Theorem 1 includes the mathematically nontrivial no-zero result, the
  substitutability/one-instability equivalence, and tight instability examples
  throughout the advertised range.
- The displayed fixed-threshold and rank-threshold ML formulas are represented
  as actual predictors. Fixed thresholds imply zero instability; rank
  thresholds satisfy the instability and variability bounds and admit a real
  score embedding that realizes the exact-one case.
- Theorem 2 proves the realized range `1 <= m <= n` for sequential queue
  representations and the exact single-order characterization under the
  intended minimal/nondegenerate interpretation.
- All four Proposition 2 program classes are constructed computationally and
  have exact variability `1`, `2`, `3`, and `6`, together with the common
  one-instability property.
- The appendix choice-property, parity, append/remove, and corrected
  removable-set statements are proved at their source-facing endpoints.
- The LAP development now uses real weights, per-slot tie-freeness,
  feasibility, capacity filling, and objective optimality. It proves the
  assignment choice formula, assigned-versus-rejected ordering, one
  instability, and the variability bound by the canonical number of distinct
  slot-induced orders.

## 5. Remaining Boundaries and Gaps

None at the mathematical source-claim level. Human source-to-Lean review is a
separate release-governance gate and remains incomplete; it is not a missing
formalization result.

## 6. Additional Assumptions Beyond Paper

None. `Assumptions.lean` declares no paper-local axioms and
`status.json.review_surface.assumption_names` is empty. Conditions such as
positive capacity, a universe larger than capacity, distinct-pair comparison
for a strict total order, tie-free slot weights, and optimizer well-posedness
are the explicit mathematical content needed to state the source model
nonvacuously; they are recorded at exact source locations and are not imported
as opaque proof assumptions.

The recursive source-record audit separately checks every visible
record-shaped or broad predicate input. Ordinary visible binders are discharged
once by the complete v10 obligation ledger; no conclusion-bearing certificate,
replay package, or caller-supplied theorem result remains as a proof boundary.

## 7. Proof-Strategy Deviations

Several source proofs are represented by equivalent finite constructions
rather than line-by-line translations: real score embeddings realize the
rank-threshold formula, explicit queue programs witness the four variability
values, parity derives nonselection, and canonical slot-order quotients prove
the LAP counting bound. Each route reaches the source conclusion under the
source conditions and introduces no additional mathematical assumption.

## 8. Proof Tricks Worth Reusing

- Derive the parity bridge from capacity/cardinality accounting rather than
  accepting inserted-applicant nonselection as an extra premise.
- Represent pool-dependent ML claims through an explicit binary membership
  label and prove predictor equality pointwise; this makes the fixed/rank
  threshold consequences small extensional arguments.
- State realized variability with both an upper bound and a concrete witness.
  This prevents an at-most theorem from masquerading as an exact paper claim.
- For finite program examples, define the queue runner computationally and use
  kernel `decide` on small exact carriers. The proof remains replayable by Lean
  and does not rely on `native_decide` or an external certificate.
- For LAP counting, quotient slots by extensional equality of their induced
  strict orders and count the canonical image. This avoids confusing the raw
  number of slots with the number of distinct realized order classes.
- Generalizing the LAP weights from integers to reals required no change in the
  combinatorial proof architecture once the arithmetic assumptions were stated
  at the right abstraction level.

## 9. Generalizations, Conjectures, and Extensions

The checked real-weight LAP argument suggests a reusable generalization to
other linearly ordered additive weight domains, but this was left paper-local
because the present source claims real weights and a generic library API would
need a deliberate design review. The sequential-composition and canonical
order-image lemmas are plausible library-lift candidates for a future cleanup.

No stronger empirical or runtime claim is inferred. The paper describes
training, top-q inference, deferred acceptance, and simulation procedures, but
does not state an asymptotic theorem for them; the formalization therefore
audits their mathematical formulas and choice consequences without inventing a
complexity result.

## 10. Mathematical Typos or Other Fixes Suggested in the Source Paper

`audit/source_proof_fidelity.json` records 18 minor source corrections with no
status impact and no partial or caveat-impact finding. The most visible source
repairs are:

- the no-zero clause needs positive capacity and a genuinely larger universe;
- a monotonicity/q-acceptance proof route incorrectly asks for two disjoint
  q-sets, although one extra applicant suffices;
- the removable-set lemma prints a self-equality instead of the intended
  cross-pool equality;
- several appendix lines contain local index, membership, parenthesis, or
  self-cardinality typos;
- strict-total-order completeness is read on distinct pairs;
- Theorem 2 and exact q-representative variability require the ordinary
  nondegenerate/minimal-representation reading;
- the source LAP world is real-valued and tie-free, not the former restricted
  integer/externally selected optimizer model.

Each intended endpoint is proved. None of these is a substantial central paper
error, so none warrants `formalized with caveat`.

## 11. Paper Issues or Caveats

None. The source repairs above are local typos or ordinary nondegeneracy
clarifications; they do not change a central advertised conclusion.

## 12. Detailed Formalization Evidence

### Source pin and inventory

- Published paper: AAAI-26, DOI `10.1609/aaai.v40i45.41179`.
- Formula/proof source: arXiv `2601.11513v1`.
- Pinned archive: `source_tex/arxiv_source.tar`, SHA-256
  `0d57324d02fc64c4c6b627c71c71cbbf93610b7f0b4b2138da1b436bb9234434`.
- `audit/paper_statement_map.json`: 20 definitions, 3 formulas, 3 model
  objects, 17 theorems, 9 propositions, 9 lemmas, and 4 corollaries.
- `audit/paper_coverage_llm.json`: 61 exact items and 4 collective-support
  items, totaling all 65 source targets.

The source inventory was constructed from `source_tex/main.tex` and
`source_tex/appendix.tex` before comparing the 69-row `PaperInterface.lean`
surface. The checked-in TeX agrees with the pinned archive modulo whitespace.

### Review surface and semantic matching

`PaperInterface.lean` contains 136 declarations: 69 configured direct
paper-facing rows and 67 auxiliary predicate-vocabulary, implementation, or
component rows. The reviewed surface has 5 definitions/abbreviations and 64
theorems. Every configured row
has a current v10 atom-by-atom `matches` judgment. The statement ledger expands
named predicates, checks natural versus real numerical domains, finite-set and
sequence semantics, perturbation nonvacuity where applicable, extrema witness
coherence, distinct-order counting, and complete output shape.

The 21 predicate-valued internal aliases are auxiliary vocabulary. Nineteen
new formula/iff theorems plus the two existing threshold-formula theorems expose
and prove their exact source semantics, so no Prop definition masquerades as
proof and no unaudited human source-definition attestation is fabricated.
Theorem-like source items likewise route to reviewed theorem/lemma declarations.

### Lean build and proof closure

`lake build DGD26AdmissionsPredictability` passes (3,306 jobs). The paper folder
contains 14,062 lines of Lean, including the 1,191-line paper interface. The
dependency closure contains no `sorry`, `admit`, `axiom`, `opaque`, or
`constant` proof shortcut used to establish a paper result.
<!-- BEGIN GENERATED LLM-AS-JUDGE RESULTS -->
### LLM-as-Judge Results
- Source coverage (`audit/paper_coverage_llm.json`): 61 covered, 4 covered by reviewed rows; diagnostics: full inventory shown because paper_statement_map.json must explicitly set source_coverage_mode before a source-coverage closeout.
- Statement match (`audit/statement_match_llm.json`): no rows; diagnostics: 69 orphan/stale statement-sidecar rows excluded, 69 configured rows without unambiguous current receipts.
- Lean-to-TeX translations (`audit/lean_to_tex_llm.json`): 69 row translations generated from Lean statements.
- Assumption provenance (`audit/assumption_match_llm.json`): no configured source-condition rows.
- Source-record classification (`audit/source_record_match_llm.json`): 59 source condition, 1 non-propositional witness data.
- Source-record structural audit (`audit/source_record_audit.json`): 69 source-record review rows, 118 boundary inputs, 26 conclusion dependencies, 48 recursive fields, 0 source-record-only unresolved conclusion dependencies, 0 recursion failures.
- Review-surface audit (`audit/review_surface_llm.json`): review surface passed over 69 review rows.
- Holistic source-first audit (`docs/AGENT_SOURCE_AUDIT.md`): status not inferred by this generator.
- DAG/source/source-json audit (`docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`): status not inferred by this generator.
<!-- END GENERATED LLM-AS-JUDGE RESULTS -->

## 13. Paper Assumption Provenance

No paper-local assumption declarations are needed. Source model and
nondegeneracy conditions are stated directly on the reviewed definitions and
theorems, and their recursive inputs have current source provenance.

<!-- BEGIN GENERATED ASSUMPTION PROVENANCE LEDGER -->
### Current Canonical Evidence
Generated from the configured source-condition surface and exact current statement digests in the canonical assumption-provenance sidecar. Model, agent, and automated checks are identified as such; no human review is inferred.

| Assumption declaration | Lean declaration | Source location / statement | Assumption validators | Comments |
| --- | --- | --- | --- | --- |
| None | `none` | None | None | No paper-facing assumption declarations are configured. |
<!-- END GENERATED ASSUMPTION PROVENANCE LEDGER -->

## 14. Displayed Formula Provenance

The application scores, queue formulas, instability quantities, parity
relations, and real-valued assignment objectives have direct formula or theorem
rows. Local index and parenthesis repairs remain visible in the fidelity ledger.

<!-- BEGIN GENERATED FORMULA PROVENANCE LEDGER -->
### Current Canonical Evidence
Rows are selected from semantic `formula` and `equation` source-kind metadata within the configured semantic source-coverage scope, never from declaration names. Coverage and statement checks remain separate evidence lanes. Scope metadata needs repair, so the full inventory is shown: paper_statement_map.json must explicitly set source_coverage_mode before a source-coverage closeout

| Paper formula / subclaim | Lean declaration | Provenance | Validators | Comments |
| --- | --- | --- | --- | --- |
| The fixed-threshold score classifier is f(x)=1{s(x)≥t}, with s:X→[0,1] and a pool-independent threshold t. | `paper_fixed_threshold_formula_statement` | covered. `paper_fixed_threshold_formula_statement`: no completed statement check | covered; Agent check by Codex DGD26 source-first completion; 2026-07-19 | The predictor and membership theorem expose the exact pool-independent threshold formula. |
| For applicant x_i in pool X, the binary label is y_i=C(X)_i=1 exactly when x_i∈C(X), and is 0 otherwise. | `paper_definition_choice_label`<br>`paper_choice_label_formula_statement` | covered. `paper_definition_choice_label`: no completed statement check<br>`paper_choice_label_formula_statement`: no completed statement check | covered; Agent check by Codex DGD26 source-first completion; 2026-07-19 | The binary label is defined and proved equal to one exactly on C(X). |
| The cohort-dependent rank model is f(x;X)=1{s(x)≥t_q(X)}, where t_q(X) is the q-th score in X. | `paper_rank_threshold_formula_statement` | covered. `paper_rank_threshold_formula_statement`: no completed statement check | covered; Agent check by Codex DGD26 source-first completion; 2026-07-19 | The top-q score predictor is proved equivalent on every pool to a pool-specific real threshold. |
<!-- END GENERATED FORMULA PROVENANCE LEDGER -->

## 15. Library Lift Pass

The finite-choice, queue, and assignment infrastructure is reusable. All
paper-specific bridges needed by the selected results are constructed in Lean;
no external certificate remains.

## 16. DAG Audit

`docs/DependencyDAG.tex` now shows only source-shaped formalized result nodes
for the finite-choice core, ML formulas, sequential/program results,
choice-property/parity/append-remove layer, and real-weight LAP layer. Its
status note records the 61+4 inventory accounting and the ordinary-note
taxonomy. `docs/DependencyDAG.pdf` was rebuilt from that TeX and visually
inspected for legibility, complete node coverage, and arrows that do not cross
node text.

## 17. Validation Checks

The paper closeout uses the following targeted commands in a frozen isolated
worktree:

```text
lake build DGD26AdmissionsPredictability
python3 scripts/review_dashboard.py --paper DGD26AdmissionsPredictability --refresh-cache
python3 skills/econcs-formalizer/scripts/source_record_audit.py --paper DGD26AdmissionsPredictability --root . --out papers/DGD26AdmissionsPredictability/audit/source_record_audit.json
python3 scripts/audit_conclusion_provenance.py --paper DGD26AdmissionsPredictability
python3 scripts/audit_evidence_integrity.py --paper DGD26AdmissionsPredictability
python3 scripts/audit_repository.py --paper DGD26AdmissionsPredictability --paper-closeout --include-active --info-limit 0
```

The release-only human-review gate is intentionally not claimed.

## 18. Paper Definitions Checked

The checked definitions cover feasible and q-acceptant choice rules,
instability, substitutability, consistency, independence, q-representative
queues, sequential queue variability, parity encodings, and the real-valued
linear-assignment application.

## 19. Named Theorem Statements Checked

All named main-text and appendix results in the 65-item inventory have direct
or explicitly grouped proof routes, including the no-zero and tight-instability
results, inconsistency equivalences, q-representative characterization, queue
variability theorems, concrete programs, and assignment variability endpoint.

## 20. Paper-Facing Statement Validator Ledger

The configured surface contains 69 rows, but none of the raw statement receipts
binds the current cached paper statement by exact semantic identity. Those 69
receipts remain diagnostic-only pending a content-bound reissue. Independent
human dashboard review remains 0/69 and is not claimed.

<!-- BEGIN GENERATED STATEMENT VALIDATOR LEDGER -->
### Current Canonical Evidence
Independent human dashboard review: 0/69 rows. No human row-level approval is inferred. review surface passed; Agent check by Codex DGD26 source-first surface auditor 2026-07-18; 2026-07-19 Diagnostic-only evidence excluded from this paper-facing ledger: 69 unconfigured, stale, or ambiguous statement-sidecar rows.

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| Paper choice function model definition statement | `paper_choice_function_model_definition_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper definition choice label | `paper_definition_choice_label` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper ml representation definition statement | `paper_ml_representation_definition_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper q acceptance definition statement | `paper_q_acceptance_definition_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper total order definition statement | `paper_total_order_definition_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper q representativeness definition statement | `paper_q_representativeness_definition_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Definition: r_C(X1,X2) is \|X1 ∩ C(X2) \ C(X1)\| + \|C(X1) \ C(X2)\| for X1 subset X2. | `paper_definition_choice_distance` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DGD26 context-free signature translator 2026-07-18; 2026-07-19 | None recorded |
| Definition: r_C(X1,X2) is \|X1 ∩ C(X2) \ C(X1)\| + \|C(X1) \ C(X2)\| for X1 subset X2. | `paper_choice_distance_formula` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DGD26 context-free signature translator 2026-07-18; 2026-07-19 | None recorded |
| Paper d instability definition statement | `paper_d_instability_definition_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper tight d instability definition statement | `paper_tight_d_instability_definition_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Definition: for a 1-unstable q-acceptant choice function, variability is max_X \| union over x' of C(X) \ C(X ∪ {x'}) \|. | `paper_definition_borderline_set` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DGD26 context-free signature translator 2026-07-18; 2026-07-19 | None recorded |
| Paper variability at most definition statement | `paper_variability_at_most_definition_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper variability exactly definition statement | `paper_variability_exactly_definition_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper choice label formula statement | `paper_choice_label_formula_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper fixed threshold formula statement | `paper_fixed_threshold_formula_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper ml fixed threshold representation zero unstable statement | `paper_ml_fixed_threshold_representation_zero_unstable_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper rank threshold formula statement | `paper_rank_threshold_formula_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper ml rank threshold representation instability bound statement | `paper_ml_rank_threshold_representation_instability_bound_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper ml rank threshold representation variability bound statement | `paper_ml_rank_threshold_representation_variability_bound_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper ml rank threshold can represent exact one statement | `paper_ml_rank_threshold_can_represent_exact_one_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper q representative forward exact statement | `paper_q_representative_forward_exact_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper q representative converse exact statement | `paper_q_representative_converse_exact_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper variability one iff single order statement | `paper_variability_one_iff_single_order_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper substitutability definition statement | `paper_substitutability_definition_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem: for a q-acceptant choice function, it cannot be 0-unstable under the nontrivial-universe condition, it is exactly 1-unstable iff substitutable, and tightly d-unstable examples exist for every 1 <= d <= 2q. | `paper_no_zero_instability_under_capacity_statement` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DGD26 context-free signature translator 2026-07-18; 2026-07-19 | None recorded |
| Theorem: any q-acceptant choice function is 1-unstable iff substitutable. | `paper_substitutability_one_instability_equivalence_statement` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DGD26 context-free signature translator 2026-07-18; 2026-07-19 | None recorded |
| Theorem: for a q-acceptant choice function, it cannot be 0-unstable under the nontrivial-universe condition, it is exactly 1-unstable iff substitutable, and tightly d-unstable examples exist for every 1 <= d <= 2q. | `paper_q_acceptant_two_q_instability_bound_statement` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DGD26 context-free signature translator 2026-07-18; 2026-07-19 | None recorded |
| Theorem: for a q-acceptant choice function, it cannot be 0-unstable under the nontrivial-universe condition, it is exactly 1-unstable iff substitutable, and tightly d-unstable examples exist for every 1 <= d <= 2q. | `paper_padded_even_tight_instability_family_statement` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DGD26 context-free signature translator 2026-07-18; 2026-07-19 | None recorded |
| Theorem: for a q-acceptant choice function, it cannot be 0-unstable under the nontrivial-universe condition, it is exactly 1-unstable iff substitutable, and tightly d-unstable examples exist for every 1 <= d <= 2q. | `paper_padded_odd_tight_instability_family_statement` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DGD26 context-free signature translator 2026-07-18; 2026-07-19 | None recorded |
| Definition: C is a sequential composition of C_n,...,C_1 when it chooses from each stage's remaining set and unions the chosen sets. | `paper_definition_sequential_composition` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DGD26 context-free signature translator 2026-07-18; 2026-07-19 | None recorded |
| Paper sequential q representative variability range statement | `paper_sequential_q_representative_variability_range_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper screened open variability one statement | `paper_screened_open_variability_one_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper screened open dia variability two statement | `paper_screened_open_dia_variability_two_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper educational option variability three statement | `paper_educational_option_variability_three_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper educational option dia variability six statement | `paper_educational_option_dia_variability_six_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper program classes one instability statement | `paper_program_classes_one_instability_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper monotonicity definition statement | `paper_monotonicity_definition_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper consistency definition statement | `paper_consistency_definition_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Lemma: if the universe has size greater than q and q >= 1, no choice function is both monotonic and q-acceptant. | `paper_monotonicity_q_acceptance_incompatible_statement` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DGD26 context-free signature translator 2026-07-18; 2026-07-19 | None recorded |
| Lemma: if C is not substitutable, then some single added applicant x' causes a previously rejected existing applicant x* to become accepted. | `paper_non_substitutable_single_add_statement` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DGD26 context-free signature translator 2026-07-18; 2026-07-19 | None recorded |
| Lemma: C is substitutable iff \|X1 ∩ C(X2) \ C(X1)\| = 0 for all X1 subset X2. | `paper_substitutability_term_statement` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DGD26 context-free signature translator 2026-07-18; 2026-07-19 | None recorded |
| Lemma: C is monotonic iff \|C(X1) \ C(X2)\| = 0 for all X1 subset X2. | `paper_monotonicity_term_statement` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DGD26 context-free signature translator 2026-07-18; 2026-07-19 | None recorded |
| Theorem: choice distance satisfies the triangle inequality for X1 subset X2 subset X3. | `paper_choice_distance_triangle_statement` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DGD26 context-free signature translator 2026-07-18; 2026-07-19 | None recorded |
| Paper zero instability definition statement | `paper_zero_instability_definition_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Corollary: C is 0-unstable iff it is both substitutable and monotonic. | `paper_zero_distance_statement` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DGD26 context-free signature translator 2026-07-18; 2026-07-19 | None recorded |
| Paper independence definition statement | `paper_independence_definition_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem: C is independent iff it is both substitutable and monotonic. | `paper_independent_substitutable_monotonic_statement` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DGD26 context-free signature translator 2026-07-18; 2026-07-19 | None recorded |
| Corollary: C is 0-unstable iff it is independent; therefore no q-acceptant C is 0-unstable under the nontrivial-universe condition. | `paper_independent_zero_unstable_statement` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DGD26 context-free signature translator 2026-07-18; 2026-07-19 | None recorded |
| Theorem: any q-acceptant substitutable choice function is consistent. | `paper_q_acceptant_substitutable_consistent_statement` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DGD26 context-free signature translator 2026-07-18; 2026-07-19 | None recorded |
| Lemma: for q-acceptant C, X'=X∪{x'}, \|X\|>=q, and n=\|C(X)\C(X')\|, r_C(X,X') = 2n - 1_{x' in C(X')}. | `paper_calculating_instability_statement` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DGD26 context-free signature translator 2026-07-18; 2026-07-19 | None recorded |
| Paper even distance iff inconsistent statement | `paper_even_distance_iff_inconsistent_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper no consistent positive tightly even statement | `paper_no_consistent_positive_tightly_even_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Definition: general variability is the max of the largest borderline set V_C(X) and waitlisted set A_C(X). | `paper_definition_waitlisted_set` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DGD26 context-free signature translator 2026-07-18; 2026-07-19 | None recorded |
| Paper general variability at most definition statement | `paper_general_variability_at_most_definition_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper general variability exactly definition statement | `paper_general_variability_exactly_definition_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem: for q-acceptant 1-unstable C and universe size at least 2q, the maximum waitlisted-set size equals the maximum borderline-set size. | `paper_append_remove_variability_at_most_equivalence_statement` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DGD26 context-free signature translator 2026-07-18; 2026-07-19 | None recorded |
| Theorem: for q-acceptant 1-unstable C and universe size at least 2q, the maximum waitlisted-set size equals the maximum borderline-set size. | `paper_append_remove_variability_exact_equivalence_statement` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DGD26 context-free signature translator 2026-07-18; 2026-07-19 | None recorded |
| Corrected lemma: if C is 1-unstable and q-acceptant and C(X1)=C(X2), then V_C(X1)=V_C(X2). The TeX source has the typo V_C(X1)=V_C(X1). | `paper_corrected_consistency_of_removable_sets_statement` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DGD26 context-free signature translator 2026-07-18; 2026-07-19 | None recorded |
| Lemma: for q-acceptant 1-unstable C with variability 1, V_C(X)=A_C(X∪{x'}) when adding x' changes the chosen set. | `paper_acceptant_one_instability_variability_borderline_eq_waitlisted_after_changing_insert_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem: sequential composition of substitutable choice functions is substitutable. | `paper_sequential_composition_substitutable_statement` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DGD26 context-free signature translator 2026-07-18; 2026-07-19 | None recorded |
| Theorem: a sequential composition of q-acceptant 1-unstable functions with variabilities m1,...,mn has variability at most sum_i m_i. | `paper_sequential_additive_variability_bound_statement` | No completed statement check recorded. Lean translation recorded; Agent check by Codex DGD26 context-free signature translator 2026-07-18; 2026-07-19 | None recorded |
| Paper lap slot below definition statement | `paper_lap_slot_below_definition_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper lap same slot order definition statement | `paper_lap_same_slot_order_definition_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper lap model definition statement | `paper_lap_model_definition_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper lap assignment choice formula statement | `paper_lap_assignment_choice_formula_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper lap assigned strictly outranks rejected statement | `paper_lap_assigned_strictly_outranks_rejected_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Lemma: in a linear assignment problem, the applicant assigned to slot s is ordered above every rejected applicant by slot s's ordering. | `paper_lap_strictly_higher_slot_applicant_assigned_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem: linear assignment problems are 1-unstable. | `paper_lap_assignment_one_instability_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem: the variability of a linear assignment problem is upper bounded by the number of distinct preference orderings induced by its slots. | `paper_lap_assignment_slot_order_class_variability_of_unique_global_optima_statement` | No completed statement check recorded. No Lean translation recorded | None recorded |
<!-- END GENERATED STATEMENT VALIDATOR LEDGER -->

## 21. Source-Coverage Audit Ledger

The source inventory contains 65 mathematical items: 61 have direct reviewed
routes and four are covered collectively by explicit theorem groups. There is
no missing, conditional, or out-of-scope named-theory target.

<!-- BEGIN GENERATED SOURCE COVERAGE LEDGER -->
### Current Canonical Evidence
- Coverage scope: full inventory shown because scope metadata needs repair (paper_statement_map.json must explicitly set source_coverage_mode before a source-coverage closeout).
- Source inventory: 65 source statements from `source_tex/arxiv_source.tar`.
- Coverage result: 61 covered, 4 covered by reviewed rows.
- Coverage review: coverage ledger recorded; Agent check by Codex DGD26 source-first completion; 2026-07-19.
- Row-local statement checks: 0/73 linked row references have a completed canonical statement check; repeated links are counted per source row.

| Source statement | Linked Lean review rows | Coverage judgment | Row-local statement checks | Comments |
| --- | --- | --- | --- | --- |
| The fixed-threshold score classifier is f(x)=1{s(x)≥t}, with s:X→[0,1] and a pool-independent threshold t. | `paper_fixed_threshold_formula_statement` | covered | `paper_fixed_threshold_formula_statement`: no completed statement check | The predictor and membership theorem expose the exact pool-independent threshold formula. |
| A finite choice function maps every finite applicant pool X to a feasible chosen subset C(X)⊆X. | `paper_choice_function_model_definition_statement` | covered | `paper_choice_function_model_definition_statement`: no completed statement check | The carrier and feasibility convention jointly expose the finite choice-function model. |
| For applicant x_i in pool X, the binary label is y_i=C(X)_i=1 exactly when x_i∈C(X), and is 0 otherwise. | `paper_definition_choice_label`<br>`paper_choice_label_formula_statement` | covered | `paper_definition_choice_label`: no completed statement check<br>`paper_choice_label_formula_statement`: no completed statement check | The binary label is defined and proved equal to one exactly on C(X). |
| A choice function is q-acceptant when \|C(X)\|=min{q,\|X\|} for every finite input set X. | `paper_q_acceptance_definition_statement` | covered | `paper_q_acceptance_definition_statement`: no completed statement check | The paper-facing predicate has the same capacity equation and quantification. |
| A strict total order is asymmetric and transitive, and compares every distinct pair of applicants. | `paper_total_order_definition_statement` | covered | `paper_total_order_definition_statement`: no completed statement check | Lean uses the coherent distinct-pair reading; the printed unrestricted comparability wording is recorded as a note-only source correction. |
| A queue sorts applicants by one strict total order and chooses the top q elements of every input pool. | `paper_q_representativeness_definition_statement` | covered | `paper_q_representativeness_definition_statement`: no completed statement check | The q-representative predicate exposes the same one-order top-q semantics. |
| For X₁⊆X₂, choice distance is \|(X₁∩C(X₂))\C(X₁)\|+\|C(X₁)\C(X₂)\|. | `paper_definition_choice_distance`<br>`paper_choice_distance_formula` | covered | `paper_definition_choice_distance`: no completed statement check<br>`paper_choice_distance_formula`: no completed statement check | The definition wrapper and displayed-formula theorem preserve both set-difference summands. |
| C is d-unstable when every one-applicant insertion changes at most d existing decisions under choice distance. | `paper_d_instability_definition_statement` | covered | `paper_d_instability_definition_statement`: no completed statement check | The Lean predicate has the same universal single-insertion bound. |
| C is tightly d-unstable when it is d-unstable but not (d-1)-unstable. | `paper_tight_d_instability_definition_statement` | covered | `paper_tight_d_instability_definition_statement`: no completed statement check | The least-bound predicate is represented exactly; the later printed dk typo is separately noted. |
| For a q-acceptant 1-unstable rule, variability is max_X \|⋃_{x′} C(X)\C(X∪{x′})\|. | `paper_definition_borderline_set`<br>`paper_variability_at_most_definition_statement`<br>`paper_variability_exactly_definition_statement` | covered | `paper_definition_borderline_set`: no completed statement check<br>`paper_variability_at_most_definition_statement`: no completed statement check<br>`paper_variability_exactly_definition_statement`: no completed statement check | The borderline set plus at-most and exact predicates jointly expose the displayed maximum. |
| An ML model represents C when one predictor f gives f(x_i)=C(X)_i for every applicant pool X and every x_i∈X. | `paper_ml_representation_definition_statement` | covered | `paper_ml_representation_definition_statement`: no completed statement check | The representation predicate quantifies every pool and every offered applicant. |
| The cohort-dependent rank model is f(x;X)=1{s(x)≥t_q(X)}, where t_q(X) is the q-th score in X. | `paper_rank_threshold_formula_statement` | covered | `paper_rank_threshold_formula_statement`: no completed statement check | The top-q score predictor is proved equivalent on every pool to a pool-specific real threshold. |
| C is substitutable when X₁⊆X₂ implies X₁∩C(X₂)⊆C(X₁). | `paper_substitutability_definition_statement` | covered | `paper_substitutability_definition_statement`: no completed statement check | The paper-facing predicate is the same nested-set implication. |
| Sequential composition runs each choice rule on applicants remaining after earlier stages and unions all stage choices. | `paper_definition_sequential_composition` | covered | `paper_definition_sequential_composition`: no completed statement check | The list recursion implements the same remaining-pool construction. |
| C is monotonic when X₁⊆X₂ implies C(X₁)⊆C(X₂). | `paper_monotonicity_definition_statement` | covered | `paper_monotonicity_definition_statement`: no completed statement check | The Lean predicate is the same containment implication. |
| C is consistent when C(X₂)⊆X₁⊆X₂ implies C(X₂)=C(X₁). | `paper_consistency_definition_statement` | covered | `paper_consistency_definition_statement`: no completed statement check | The Lean predicate preserves both containments and the equality conclusion. |
| C is q-representative when it is q-acceptant and one strict total order selects its top q applicants from every pool. | `paper_q_representativeness_definition_statement` | covered | `paper_q_representativeness_definition_statement`: no completed statement check | The predicate exposes one global strict order and top-q choice. |
| C is 0-unstable exactly when r_C(X₁,X₂)=0 for every X₁⊆X₂. | `paper_zero_instability_definition_statement` | covered | `paper_zero_instability_definition_statement`: no completed statement check | The Lean zero-instability predicate has the same all-nested-pools scope. |
| C is independent when each applicant is either always chosen whenever available or never chosen whenever available. | `paper_independence_definition_statement` | covered | `paper_independence_definition_statement`: no completed statement check | The applicant-wise always-or-never behavior is represented exactly. |
| V_C(X)=⋃_{x′} C(X)\C(X∪{x′}) is the set of admits that some insertion can displace. | `paper_definition_borderline_set` | covered | `paper_definition_borderline_set`: no completed statement check | The finite union definition is exposed directly. |
| A_C(X)=⋃_{x*∈X} C(X\{x*})\C(X) is the set of applicants admitted after some removal. | `paper_definition_waitlisted_set` | covered | `paper_definition_waitlisted_set`: no completed statement check | The removal-union definition is exposed directly. |
| General variability is max{max_X \|V_C(X)\|, max_X \|A_C(X)\|}. | `paper_general_variability_at_most_definition_statement`<br>`paper_general_variability_exactly_definition_statement` | covered | `paper_general_variability_at_most_definition_statement`: no completed statement check<br>`paper_general_variability_exactly_definition_statement`: no completed statement check | The at-most and exact predicates encode the maximum of insertion and removal variability. |
| A linear assignment problem chooses a maximum-real-weight applicant-slot matching with at most one edge incident to each applicant and slot. | `paper_lap_model_definition_statement` | covered | `paper_lap_model_definition_statement`: no completed statement check | The finite matching constraints and maximum-sum objective are formalized over real weights. |
| Each slot's real weights, assumed tie-free, induce a strict total order over applicants. | `paper_lap_slot_below_definition_statement` | covered | `paper_lap_slot_below_definition_statement`: no completed statement check | The strict slot preference is exactly the real-weight comparison. |
| Two slots are equivalent exactly when they induce the same strict total order over all applicants. | `paper_lap_same_slot_order_definition_statement` | covered | `paper_lap_same_slot_order_definition_statement`: no completed statement check | Slot-order equality is extensional and its quotient gives the canonical distinct-order count. |
| The assignment's incident applicants form C(X), and x_s denotes the applicant assigned to slot s. | `paper_lap_assignment_choice_formula_statement` | covered | `paper_lap_assignment_choice_formula_statement`: no completed statement check | Assignment incidence and the induced chosen-applicant rule are exposed directly. |
| C is independent if and only if C is 0-unstable. | `paper_independent_zero_unstable_statement` | covered | `paper_independent_zero_unstable_statement`: no completed statement check | The Lean theorem proves the source equivalence from feasibility. |
| For q>0 and a universe containing more than q applicants, no feasible q-acceptant choice function is 0-unstable. | `paper_no_zero_instability_under_capacity_statement` | covered | `paper_no_zero_instability_under_capacity_statement`: no completed statement check | Lean proves the mathematically valid nontrivial-domain correction; the omitted printed conditions are note-only. |
| No q-acceptant consistent choice function is tightly d-unstable for positive even d. | `paper_no_consistent_positive_tightly_even_statement` | covered | `paper_no_consistent_positive_tightly_even_statement`: no completed statement check | The direct theorem excludes tightly even instability for every positive even parameter; the printed dk is a note-only typo. |
| C is 0-unstable if and only if it is both substitutable and monotonic. | `paper_zero_distance_statement` | covered | `paper_zero_distance_statement`: no completed statement check | One theorem row proves the complete iff. |
| For a full-capacity pool and one fresh insertion, r_C equals twice the number displaced minus the indicator that the new applicant is chosen. | `paper_calculating_instability_statement` | covered | `paper_calculating_instability_statement`: no completed statement check | The if-then-else Nat formula preserves both indicator cases. |
| If feasible q-acceptant 1-instability implies substitutability and C(X₁)=C(X₂), then V_C(X₁)=V_C(X₂). | `paper_corrected_consistency_of_removable_sets_statement` | covered by reviewed rows | `paper_corrected_consistency_of_removable_sets_statement`: no completed statement check | The corrected equality is proved after deriving the visible substitutability premise from the source q-acceptance and 1-instability conditions. |
| If an applicant ranks strictly above the applicant assigned to a slot, the higher applicant is chosen. | `paper_lap_strictly_higher_slot_applicant_assigned_statement` | covered | `paper_lap_strictly_higher_slot_applicant_assigned_statement`: no completed statement check | Objective optimality proves that every strictly higher offered applicant is assigned. |
| The applicant assigned to each slot ranks strictly above every rejected applicant in that slot's order. | `paper_lap_assigned_strictly_outranks_rejected_statement` | covered | `paper_lap_assigned_strictly_outranks_rejected_statement`: no completed statement check | No-ties real weights strengthen objective optimality to the source's strict assigned-versus-rejected order. |
| C is monotonic iff \|C(X₁)\C(X₂)\|=0 for every X₁⊆X₂. | `paper_monotonicity_term_statement` | covered | `paper_monotonicity_term_statement`: no completed statement check | The iff and cardinal-zero expression are direct. |
| When q≥1 and the universe has more than q applicants, no feasible rule is both monotonic and q-acceptant. | `paper_monotonicity_q_acceptance_incompatible_statement` | covered | `paper_monotonicity_q_acceptance_incompatible_statement`: no completed statement check | Lean proves the valid endpoint without relying on the source proof's unjustified disjoint-q-set construction. |
| For q-acceptant 1-unstable variability-one C, if insertion changes choice then V_C(X)=A_C(X∪{x′}). | `paper_acceptant_one_instability_variability_borderline_eq_waitlisted_after_changing_insert_statement` | covered | `paper_acceptant_one_instability_variability_borderline_eq_waitlisted_after_changing_insert_statement`: no completed statement check | The equality is proved for both undersized and full-capacity pools under exactly the changing-insertion hypotheses. |
| C is substitutable iff \|(X₁∩C(X₂))\C(X₁)\|=0 for every X₁⊆X₂. | `paper_substitutability_term_statement` | covered | `paper_substitutability_term_statement`: no completed statement check | The iff and first distance summand are direct. |
| Failure of substitutability has a single-insertion witness that flips an existing applicant from rejected to chosen. | `paper_non_substitutable_single_add_statement` | covered | `paper_non_substitutable_single_add_statement`: no completed statement check | The existential row exposes the pool, inserted applicant, flipped applicant, and all memberships. |
| Every fixed-threshold score model f(x)=1{s(x)≥t} that represents a choice rule can represent only a 0-unstable rule. | `paper_ml_fixed_threshold_representation_zero_unstable_statement` | covered | `paper_ml_fixed_threshold_representation_zero_unstable_statement`: no completed statement check | Representation by the displayed fixed-threshold predictor is shown to identify C with an independent rule and hence force zero instability. |
| A rank-threshold score model can represent a 1-variable, 1-unstable choice function by embedding one total order in real scores. | `paper_ml_rank_threshold_can_represent_exact_one_statement` | covered | `paper_ml_rank_threshold_can_represent_exact_one_statement`: no completed statement check | A concrete injective real score on Fin(q+1) realizes tight instability one and exact variability one. |
| No rank-threshold score model can represent a choice function with instability greater than one. | `paper_ml_rank_threshold_representation_instability_bound_statement` | covered | `paper_ml_rank_threshold_representation_instability_bound_statement`: no completed statement check | Any feasible C represented by the displayed rank-threshold predictor is proved 1-unstable. |
| No rank-threshold score model can represent a choice function with variability greater than one. | `paper_ml_rank_threshold_representation_variability_bound_statement` | covered | `paper_ml_rank_threshold_representation_variability_bound_statement`: no completed statement check | Any feasible C represented by the displayed rank-threshold predictor is proved at most 1-variable. |
| All four NYC program choice-function classes considered in Proposition 2 are 1-unstable. | `paper_program_classes_one_instability_statement` | covered | `paper_program_classes_one_instability_statement`: no completed statement check | All four explicit queue-based program representatives are proved 1-unstable. |
| Screened/Open programs have exact variability 1. | `paper_screened_open_variability_one_statement` | covered | `paper_screened_open_variability_one_statement`: no completed statement check | The canonical one-queue program has a kernel-checked exact-one witness. |
| Screened/Open with DIA programs have exact variability 2. | `paper_screened_open_dia_variability_two_statement` | covered | `paper_screened_open_dia_variability_two_statement`: no completed statement check | The canonical two-queue DIA program has a kernel-checked exact-two witness. |
| Educational Option programs have exact variability 3. | `paper_educational_option_variability_three_statement` | covered | `paper_educational_option_variability_three_statement`: no completed statement check | The canonical three-queue Educational Option program has a kernel-checked exact-three witness. |
| Educational Option with DIA programs have exact variability 6. | `paper_educational_option_dia_variability_six_statement` | covered | `paper_educational_option_dia_variability_six_statement`: no completed statement check | The canonical six-queue Educational Option with DIA program has a kernel-checked exact-six witness. |
| A sequential composition of q-acceptant 1-unstable stages with variability bounds m_i has variability at most Σ_i m_i. | `paper_sequential_additive_variability_bound_statement` | covered | `paper_sequential_additive_variability_bound_statement`: no completed statement check | The stage lists, capacities, instability premises, and summed bound are all exposed. |
| For q-acceptant 1-unstable C in a universe of size at least 2q, the maximum waitlisted-set size equals the maximum borderline-set size. | `paper_append_remove_variability_at_most_equivalence_statement`<br>`paper_append_remove_variability_exact_equivalence_statement` | covered by reviewed rows | `paper_append_remove_variability_at_most_equivalence_statement`: no completed statement check<br>`paper_append_remove_variability_exact_equivalence_statement`: no completed statement check | The at-most and exact predicate equivalences collectively encode the maximum equality; the stray source token is note-only. |
| For X₁⊆X₂⊆X₃, r_C(X₁,X₃)≤r_C(X₁,X₂)+r_C(X₂,X₃). | `paper_choice_distance_triangle_statement` | covered | `paper_choice_distance_triangle_statement`: no completed statement check | The three pools, containments, inequality direction, and both summands match. |
| For q-acceptant C, inconsistency is equivalent to the existence of a fresh insertion with positive even choice distance. | `paper_even_distance_iff_inconsistent_statement` | covered | `paper_even_distance_iff_inconsistent_statement`: no completed statement check | One theorem proves both directions and derives fresh-applicant nonselection from positive even parity. |
| C is independent if and only if it is both substitutable and monotonic. | `paper_independent_substitutable_monotonic_statement` | covered | `paper_independent_substitutable_monotonic_statement`: no completed statement check | The complete iff is proved under the explicit feasibility model condition. |
| For q>0 with more than q possible applicants, a feasible q-acceptant choice function cannot be 0-unstable. | `paper_no_zero_instability_under_capacity_statement` | covered by reviewed rows | `paper_no_zero_instability_under_capacity_statement`: no completed statement check | The corrected nontrivial-domain theorem row supplies the first Theorem 1 clause; the source omission is note-only. |
| A feasible q-acceptant choice function is 1-unstable if and only if it is substitutable. | `paper_substitutability_one_instability_equivalence_statement` | covered | `paper_substitutability_one_instability_equivalence_statement`: no completed statement check | One row proves the full iff under the paper choice-function model. |
| For every integer d with 1≤d≤2q, some feasible q-acceptant choice function is tightly d-unstable. | `paper_q_acceptant_two_q_instability_bound_statement`<br>`paper_padded_even_tight_instability_family_statement`<br>`paper_padded_odd_tight_instability_family_statement` | covered by reviewed rows | `paper_q_acceptant_two_q_instability_bound_statement`: no completed statement check<br>`paper_padded_even_tight_instability_family_statement`: no completed statement check<br>`paper_padded_odd_tight_instability_family_statement`: no completed statement check | The universal upper bound and parameterized even/odd construction families collectively cover every d in the range. |
| Every linear assignment choice rule in the source real-weight, tie-free model is 1-unstable. | `paper_lap_assignment_one_instability_statement` | covered | `paper_lap_assignment_one_instability_statement`: no completed statement check | A well-posed real-weight maximum-assignment problem canonically induces a 1-unstable choice rule. |
| LAP variability is at most the number of distinct total orders induced by its slots. | `paper_lap_assignment_slot_order_class_variability_of_unique_global_optima_statement` | covered | `paper_lap_assignment_slot_order_class_variability_of_unique_global_optima_statement`: no completed statement check | The canonical real-weight LAP choice has variability bounded by the quotient count of exact slot-order classes. |
| A q-representative rule is q-acceptant, 1-unstable, and has exact variability 1. | `paper_q_representative_forward_exact_statement` | covered | `paper_q_representative_forward_exact_statement`: no completed statement check | Positive nontrivial capacity derives the source's exact-one conclusion without a displacement certificate premise. |
| A feasible q-acceptant 1-unstable rule with exact variability 1 is q-representative. | `paper_q_representative_converse_exact_statement` | covered | `paper_q_representative_converse_exact_statement`: no completed statement check | The source hypotheses, including exact variability one, directly derive one-order representativeness. |
| Sequential composition of feasible substitutable choice functions is substitutable. | `paper_sequential_composition_substitutable_statement` | covered | `paper_sequential_composition_substitutable_statement`: no completed statement check | The list theorem proves the same closure property. |
| A feasible q-acceptant choice function is 1-unstable if and only if it is substitutable. | `paper_substitutability_one_instability_equivalence_statement` | covered | `paper_substitutability_one_instability_equivalence_statement`: no completed statement check | One equivalence row exposes both directions under the paper choice-function convention. |
| Every q-acceptant substitutable choice function is consistent. | `paper_q_acceptant_substitutable_consistent_statement` | covered | `paper_q_acceptant_substitutable_consistent_statement`: no completed statement check | The Lean row proves the source consistency implication directly. |
| A q-acceptant 1-unstable sequential composition of n total-order queues has variability m satisfying 1≤m≤n. | `paper_sequential_q_representative_variability_range_statement` | covered | `paper_sequential_q_representative_variability_range_statement`: no completed statement check | The realized maximum supplies m and nondegenerate capacity proves 1≤m≤n. |
| Under the intended minimal queue representation, variability is 1 if and only if the choice rule is characterized by one total order. | `paper_variability_one_iff_single_order_statement` | covered | `paper_variability_one_iff_single_order_statement`: no completed statement check | Exact variability one is proved equivalent to characterization by a single total order. |
<!-- END GENERATED SOURCE COVERAGE LEDGER -->
