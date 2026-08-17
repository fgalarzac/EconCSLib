# Final Validation Report: GJ18 Informative Rating Systems

Updated: 2026-07-31

## 1. Human Verdict

The author-approved corrected finite-chain model is formalized. This does not
certify that the pinned archive already states the same model: every correction
is disclosed below and no derivation from the archive's state recurrence is
claimed. No independent human source review or release certification has been
performed.

## 2. Closeout Status

`Formalized` for the corrected governing model recorded in the
[governing-model clarification](docs/GOVERNING_MODEL_CLARIFICATION.md).
This is a corrected-model closeout, not an assertion of archival equivalence.
The archived paper remains pinned as a source baseline and its differences from
the governing model remain visible in the audit record.

- Completion status: formalized.

## 3. Source and Scope

- Paper: *Designing Informative Rating Systems: Evidence from an Online Labor
  Market*.
- Authors: Nikhil Garg and Ramesh Johari.

The archival baseline is `source.tar.gz`, SHA-256
`b5378ae6f1ada1674d9f07dd4c1405655a9109e89a9977debab1b89d599f19de`.
The public source is the
[published Management Science article](https://doi.org/10.1287/msom.2020.0921).
The governing target is the finite ordinal iid model authorized on 2026-07-24,
not a claim that the archive's `mu_k` display already derives a product law.

[PaperInterface.lean](PaperInterface.lean) is the 21-row paper-facing review
surface. It proves the corrected finite-real representation of the
extended-rate Theorem 1 endpoint as well as the state-level result. Historical
`AuditInterface.lean` material is not a closeout surface.

### Source and review receipt

The final raw source-record receipt is
`d4f6cdd7c735c1888355132483e0add4d11a5f49e0f4f5e43fb958955f29029c`,
with independent raw-integrity receipt
`0137dffc445bb72945fe3745657644a4ab28cea933cbf6e4452294bfd1a5aa99`.
It records 39 source-record judgments. The strict high/low seller-pair subtype
in the Appendix endpoints is source scope, not an additional premise: the
pinned TeX establishes the ordered type convention and strict-pair summation
at `sources/arxiv.tex:665`, `721-731`, and `1714-1718`.

Normal named-theory hidden-premise auditing is selected only by a current
receipt's exact qualified declaration, source bytes, and elaborated signature.
It does not use row names, function names, or source-map labels as a waiver.
Deep mode retains the full surface. Aggregate-only semantic rows may carry an
exact Lean route identity for this selection, but remain ineligible for
item-level judgment reuse.

## 4. Researcher Summary of Checked Results

The checked development supplies the finite type carrier, exact pair
normalization, corrected aggregate indexing, ordinal-tail comparisons, iid
floor-sample state law, and the `P_k` and `W_k` objectives. It proves strict
finite ordinal score separation, support-aware large-deviation bounds,
`P_k -> 1`, `W_k -> 1`, and the corrected Theorem 1 exponential rate.

The rate uses `WithTop Real` inside its variational expression and then proves
the corrected finite-chain minimum has an ordinary-real representative. The
binary endpoint and larger-scale cases are both covered without assuming
terminal full rating support.

## 5. Remaining Boundaries and Gaps

There is no open Lean proof obligation for the author-approved corrected model.
The remaining boundary is archival: the pinned TeX source does not itself
state all governing clauses, and no theorem derives the corrected iid law or
extended-rate codomain from its `mu_k` recurrence or unrestricted real display.
That is an explicit source-version delta, not a hidden assumption or a claim
that the archive has been silently repaired.

No independent human source-to-Lean review or release certification has been
recorded. The review ledger has 0/21 human-reviewed paper-facing rows, so this
closeout is not release-certified.

## 6. Additional Assumptions Beyond Paper

The governing correction record makes the following conditions explicit rather
than attributing them to the archive:

- at least two ordered seller types with a uniform prior;
- `0 < g(theta) <= 1` for every type;
- an aggregate over exactly `floor(k * g(theta))` observations;
- at least two ordered rating levels, strict scores, and strict cross-type
  tails only above the bottom cutoff;
- conditional iid ratings and independent seller histories at each horizon;
- the valid adjacent-pair range `0 <= i <= M - 2`;
- an extended-real variational rate with a separately proved finite final
  representative; and
- a finite-product Appendix argument, including the fixed-constant comparison
  from weak inversion to `1 - P_k`.

Each correction has an archive anchor and relation in the governing-model
record and in the source-fidelity ledger.
The complete finite-chain specification is in the
[governing-model clarification](docs/GOVERNING_MODEL_CLARIFICATION.md).

## 7. Proof-Strategy Deviations

The formal proof replaces the archive's informal recurrence-to-product-law
step with the explicit iid finite-product state law. It replaces the
continuum/Laplace Appendix transfer with a finite-support argument and keeps
the rate extended-real until finiteness is established. These changes repair
the target model; they are not presented as derivations from the archived
formulas.

## 8. Proof Tricks Worth Reusing

For finite ordinal models, prove score separation by selecting actual support
endpoints rather than manufacturing terminal full support. Keep large-deviation
objects extended-real through minimization, then prove a finite representative
only at the final theorem boundary. Make joint-law completion a visible model
field, not an inference from a suggestive recurrence name.

## 9. Generalizations, Conjectures, and Extensions

A future source revision could state the corrected theorem directly with an
extended-real rate. A real-only variant would need an explicit effective
support restriction and a proof that its rate is finite. A separate theorem
could derive the finite-chain model from a fully specified population/state
process rather than taking the iid horizon law as a governing clause.

## 10. Mathematical Typos or Other Fixes Suggested in the Source Paper

The governing record identifies three presentation repairs: the aggregate
summation endpoint, the final valid adjacent-pair index, and the real-valued
unrestricted rate display. It also replaces the unsupported Appendix transfer
by a finite discrete proof. These are source-edit suggestions, not claims that
the pinned archive already contains the corrected text.

## 11. Paper Issues or Caveats

The literal unrestricted real pairwise infimum can be zero at an
out-of-support threshold while the correct event rate is positive; an
eventually impossible event can instead have infinite cost. The archive's
`mu_k` recurrence is not treated as a proof of the iid product law. These
facts are documented in the source-fidelity ledger and governing-model record.

## 12. Detailed Formalization Evidence

The corrected model is implemented by
[ClarifiedSourceModel.lean](ClarifiedSourceModel.lean), with its state,
comparison, and rate bridges in
[SourceStateCompletion.lean](SourceStateCompletion.lean),
[SourceModelBridge.lean](SourceModelBridge.lean), and
[SourceRatePositivity.lean](SourceRatePositivity.lean). The paper-facing
endpoints are in [PaperInterface.lean](PaperInterface.lean).

The [governing-model clarification](docs/GOVERNING_MODEL_CLARIFICATION.md)
records each archival delta and links it to the governing model instead of
treating an archived formula as silently strengthened. The current semantic contract is
[corrected_model_semantic_contract.json](audit/corrected_model_semantic_contract.json);
the structural source record is
[source_record_audit.json](audit/source_record_audit.json). Neither document
claims archival derivation. Contract schema 3 binds the current semantic
surface: three named source results, six explicit assumptions, and two exact
fully qualified corrected targets (with the finite-real target deduplicated
across those routes). It records item-level freshness only for the three
source-content identities; the state-level target and assumption rows are
explicitly aggregate-audit fresh because no source-content item identity is
invented for them. It pins both the raw source-record payload and its
independent raw-integrity receipt, and maps all 14 structurally reachable
governing-model fields: nine direct `ClarifiedSourceModel` fields and five
independently mapped nested `FiniteOrdinalSourceModel` fields. A parent record
does not substitute for the nested score, schedule, or tail conditions.

Both corrected `PaperInterface.lean` target theorems were checked with
`#print axioms`. Their closure contains only `propext`, `Classical.choice`,
and `Quot.sound`; it contains no paper-specific axiom, `sorry`, or admitted
proof obligation.

## 13. Paper Assumption Provenance

The corrected finite iid model, ordered seller-pair scope, finite-state
conditions, and extended-rate domains are stated explicitly on the reviewed
surface. Their source or author-approved corrected-model provenance is recorded
at premise level; no theorem conclusion is accepted through a hidden record.

<!-- BEGIN GENERATED ASSUMPTION PROVENANCE LEDGER -->
### Current Canonical Evidence
Generated from the configured source-condition surface and exact current statement digests in the canonical assumption-provenance sidecar. Model, agent, and automated checks are identified as such; no human review is inferred.

| Assumption declaration | Lean declaration | Source location / statement | Assumption validators | Comments |
| --- | --- | --- | --- | --- |
| Source match schedule coherence | `source_match_schedule_coherence` | Source location: sources/arxiv.tex:669-670; docs/GOVERNING_MODEL_CLARIFICATION.md. - The source's ordered finite-chain match-rate and one-match schedule model. | additional assumption; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26 | The source explicitly gives a nondecreasing match function and at-most-one matching prose; the exact floor-step coherence and nonnegativity used by Lean are recorded through the governing-model condition `0 < g(theta) <= 1`. Premise-level checks: 2 additional assumption, 1 source condition |
| Source rating scores in unit interval | `source_rating_scores_in_unit_interval` | Source location: sources/arxiv.tex:679-680. - Source model: rating scores take values in the displayed interval `[0, 1]`. | source condition; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26 | The source explicitly restricts each rating score to the interval [0,1], matching the two-sided real inequality in the Lean predicate. Premise-level checks: 1 source condition |
| Source strictly increasing rating scores | `source_strictly_increasing_rating_scores` | Source location: sources/arxiv.tex:744-745; docs/GOVERNING_MODEL_CLARIFICATION.md. - Source model: the displayed rating score is strictly increasing. | additional assumption; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26 | Strict score monotonicity is an explicit finite-ordinal governing-model clause; it is not inferred from the weaker [0,1] range condition. Premise-level checks: 1 additional assumption |
| Source strict ordinal cumulative tail decrease at displayed cutoffs | `source_strict_ordinal_cumulative_tail_decrease_at_displayed_cutoffs` | Source location: sources/arxiv.tex:683; docs/GOVERNING_MODEL_CLARIFICATION.md. - Literal source-tail contract: for each pair of adjacent *displayed* cutoffs, the cumulative tail strictly decreases. Its index `r : Fin m` deliberately omits the terminal rating, because the source has no displayed cutoff above it. | source condition; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26 | The source says cumulative rating tails strictly decrease with rating level. Lean states that only between adjacent displayed cutoffs, avoiding an invented cutoff above the finite maximum. Premise-level checks: 1 source condition |
| Source strict ordinal quality tail increase above bottom | `source_strict_ordinal_quality_tail_increase_above_bottom` | Source location: sources/arxiv.tex:683; docs/GOVERNING_MODEL_CLARIFICATION.md. - Corrected ordinal quality condition: a higher seller has a strictly larger upper tail at every nonbottom displayed cutoff. Strictness at cutoff zero is intentionally excluded, since that tail is always one; the pinned archive's all-cutoff wording is recorded separately as a source-model delta. | additional assumption; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26 | The archive says tails strictly increase with quality, but strictness at the bottom cutoff is impossible because that upper tail is always one. The clarification restricts strictness to nonbottom displayed cutoffs. Premise-level checks: 1 additional assumption |
| Assumption positive match rates | `assumption_positive_match_rates` | Source location: docs/GOVERNING_MODEL_CLARIFICATION.md. - Sellers receive positive asymptotic match/sample rates. | additional assumption; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26 | Positive match rates are explicit in the governing model so every seller's floor sample count diverges; the archive's nondecreasing-rate prose alone does not establish positivity. Premise-level checks: 1 additional assumption |
<!-- END GENERATED ASSUMPTION PROVENANCE LEDGER -->

## 14. Displayed Formula Provenance

The finite-state recurrence, transition probabilities, seller-pair rates, and
extended-rate objective have direct reviewed formulas under the governing
corrected model. The report does not claim that the archival recurrence derives
the corrected product law.

<!-- BEGIN GENERATED FORMULA PROVENANCE LEDGER -->
### Current Canonical Evidence
Rows are selected from semantic `formula` and `equation` source-kind metadata within the configured semantic source-coverage scope, never from declaration names. Coverage and statement checks remain separate evidence lanes. Active coverage mode: named theoretical statements.

| Paper formula / subclaim | Lean declaration | Provenance | Validators | Comments |
| --- | --- | --- | --- | --- |
| None | `none` | None | None | No source-map row is canonically classified as a formula or equation. |
<!-- END GENERATED FORMULA PROVENANCE LEDGER -->

## 15. Library Lift Pass

Finite probability and rate-optimization support is reusable. The governing
model distinction is paper-specific and remains visible rather than being
folded into a generic library assumption.

## 16. DAG Audit

[DependencyDAG.tex](docs/DependencyDAG.tex) and its rendered
[DependencyDAG.pdf](docs/DependencyDAG.pdf) remain the dependency diagram for
this paper. A rendered visual inspection confirms a nonempty diagram; the
corrected-model modules and their paper-facing interface remain the relevant
route for this closeout rather than the historical audit wrapper.

## 17. Validation Checks
<!-- BEGIN GENERATED LLM-AS-JUDGE RESULTS -->
### LLM-as-Judge Results
- Source coverage (`audit/paper_coverage_llm.json`): 4 corrected target covered; diagnostics: 7 selected source row without coverage evidences.
- Statement match (`audit/statement_match_llm.json`): 21 exact match; resolutions: 4 approved corrected source target; source conditions: 2 source condition, 4 additional assumption.
- Lean-to-TeX translations (`audit/lean_to_tex_llm.json`): 21 row translations generated from Lean statements.
- Assumption provenance (`audit/assumption_match_llm.json`): 2 source condition, 4 additional assumption.
- Source-record classification (`audit/source_record_match_llm.json`): 4 derived, 11 visible formalization boundary, 7 source condition, 1 recursively audited support, 6 non-propositional witness data, 10 semantic model review.
- Source-record structural audit (`audit/source_record_audit.json`): 10 source-record review rows (from 27 configured review-surface rows), 13 boundary inputs, 6 conclusion dependencies, 16 recursive fields, 10 semantic-model records, 6 source-record-only unresolved conclusion dependencies, 0 recursion failures.
- Review-surface audit (`audit/review_surface_llm.json`): review surface passed over 27 review rows.
- Holistic source-first audit (`docs/AGENT_SOURCE_AUDIT.md`): status not inferred by this generator.
- DAG/source/source-json audit (`docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`): status not inferred by this generator.
<!-- END GENERATED LLM-AS-JUDGE RESULTS -->


Focused checks for this closeout are:

```bash
python3 scripts/review_dashboard.py --paper GJ18InformativeRatingSystems --source-inventory-precheck
python3 scripts/review_dashboard.py --paper GJ18InformativeRatingSystems --precheck
python3 scripts/review_dashboard.py --paper GJ18InformativeRatingSystems --source-to-lean-check
python3 scripts/audit_evidence_integrity.py --paper GJ18InformativeRatingSystems --include-source-obligations
python3 scripts/audit_conclusion_provenance.py --paper GJ18InformativeRatingSystems
python3 scripts/audit_repository.py --paper GJ18InformativeRatingSystems --paper-closeout --include-active --info-limit 0
env LEAN_NUM_THREADS=1 lake build GJ18InformativeRatingSystems
```

On 2026-07-26 these commands completed with no audit errors; the evidence gate
reported only the retained non-release-certification warnings (0/21 human
source-to-Lean review and shared statement/coverage reviewer identity). The
focused Lean build validates the corrected proof target. The audit commands
check the explicit corrected-model scope contract; they do not replace human
source review or certify the archival source as equivalent.

## 18. Paper Definitions Checked

The checked definitions cover the corrected finite ordinal iid state model,
seller types, transition and response probabilities, pairwise rates, feasible
designs, and the extended-rate objective.

## 19. Named Theorem Statements Checked

The four selected corrected-model result clusters include the finite-state
representation, state-level rate theorem, finite-real extended-rate endpoint,
and the appendix seller-pair conclusions. Their corrected-model status is
explicit in each paper-facing statement.

## 20. Paper-Facing Statement Validator Ledger

The semantic review surface contains 27 rows: 21 statements and six explicit
source or corrected-model conditions, all with current content-bound receipts.
The saved human dashboard counter remains 0/21 and does not certify the larger
semantic surface. Exact row evidence is stored under `audit/`.

<!-- BEGIN GENERATED STATEMENT VALIDATOR LEDGER -->
### Current Canonical Evidence
Independent human dashboard review: 0/21 rows. No human row-level approval is inferred. review surface passed; Recorded check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| The source defines the number of matches/ratings received by seller type theta by time k as n_k(theta)=floor(k g(theta)). | `source_definition_floor_sample_count_formula` | exact match; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26. Lean translation recorded; Agent check by Codex GJ18 context-free Lean translator 2026-07-26; 2026-07-26 | The judgment compares the source target's carrier, law, event/order boundary, arithmetic convention, and conclusion against the expanded Lean signature atom by atom. |
| For each seller type theta and horizon k, if n_k(theta) = floor(k g(theta)), the aggregate score averages exactly n_k(theta) rating scores over a finite family indexed by Fin n_k(theta); the zero-sample convention remains explicit. | `source_definition_aggregate_score_formula` | exact match; approved corrected source target; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26. Lean translation recorded; Agent check by Codex GJ18 context-free Lean translator 2026-07-26; 2026-07-26 | The judgment compares each expanded Lean binder and conclusion against the explicit author-approved corrected target, retaining the archival statement as a non-equivalence baseline. |
| For theta_hi>theta_lo, P_k(theta_hi,theta_lo) is the conditional probability of a strict correct aggregate-score ordering minus the conditional probability of a strict reversed ordering. | `source_definition_pairwise_objective_formula` | exact match; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26. Lean translation recorded; Agent check by Codex GJ18 context-free Lean translator 2026-07-26; 2026-07-26 | The judgment compares the source target's carrier, law, event/order boundary, arithmetic convention, and conclusion against the expanded Lean signature atom by atom. |
| W_k is 2/(M(M-1)) times the sum of P_k over strict ordered seller-quality pairs. | `source_definition_uniform_ranking_objective_formula` | exact match; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26. Lean translation recorded; Agent check by Codex GJ18 context-free Lean translator 2026-07-26; 2026-07-26 | The judgment compares the source target's carrier, law, event/order boundary, arithmetic convention, and conclusion against the expanded Lean signature atom by atom. |
| For at least two seller types, the source coefficient 2/(M(M-1)) equals the inverse cardinality of the strict ordered comparison-pair carrier. | `source_definition_uniform_ranking_normalization` | exact match; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26. Lean translation recorded; Agent check by Codex GJ18 context-free Lean translator 2026-07-26; 2026-07-26 | The judgment compares the source target's carrier, law, event/order boundary, arithmetic convention, and conclusion against the expanded Lean signature atom by atom. |
| Under an explicitly defined finite IID completion at horizon k, the literal state-level P_k equals the existing two-seller floor-sample P_k objective for the same ordered pair. | `source_iid_completion_pairwise_objective_bridge` | exact match; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26. Lean translation recorded; Agent check by Codex GJ18 context-free Lean translator 2026-07-26; 2026-07-26 | The judgment compares the source target's carrier, law, event/order boundary, arithmetic convention, and conclusion against the expanded Lean signature atom by atom. |
| Under the explicit finite IID completion, the source-state non-strict score-gap event equals the two-seller floor-sample weak-inversion probability used in the Appendix rate argument. | `source_iid_completion_weak_inversion_bridge` | exact match; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26. Lean translation recorded; Agent check by Codex GJ18 context-free Lean translator 2026-07-26; 2026-07-26 | The judgment compares the source target's carrier, law, event/order boundary, arithmetic convention, and conclusion against the expanded Lean signature atom by atom. |
| Under the explicit finite IID completion and at least two seller types, the literal state-level W_k equals the finite uniform floor-count ranking objective. | `source_iid_completion_uniform_ranking_objective_bridge` | exact match; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26. Lean translation recorded; Agent check by Codex GJ18 context-free Lean translator 2026-07-26; 2026-07-26 | The judgment compares the source target's carrier, law, event/order boundary, arithmetic convention, and conclusion against the expanded Lean signature atom by atom. |
| Author-confirmed clarified-model row: the record's finite seller-type prior equals the explicit uniform PMF on the nonempty ordered carrier Fin n. | `author_confirmed_clarified_uniform_type_prior` | exact match; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26. Lean translation recorded; Agent check by Codex GJ18 context-free Lean translator 2026-07-26; 2026-07-26 | The judgment compares the source target's carrier, law, event/order boundary, arithmetic convention, and conclusion against the expanded Lean signature atom by atom. |
| Author-confirmed clarified-model row: at every horizon k, the recorded state law equals the finite product law of conditionally IID ratings given seller type and independent seller histories. | `author_confirmed_clarified_iid_state_law` | exact match; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26. Lean translation recorded; Agent check by Codex GJ18 context-free Lean translator 2026-07-26; 2026-07-26 | The judgment compares the source target's carrier, law, event/order boundary, arithmetic convention, and conclusion against the expanded Lean signature atom by atom. |
| Lambda(z\|theta) is the logarithm of the finite sum over rating levels of rho(theta,y\|Y) exp(z phi(y)). | `source_definition_log_mgf_formula` | exact match; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26. Lean translation recorded; Agent check by Codex GJ18 context-free Lean translator 2026-07-26; 2026-07-26 | The judgment compares the source target's carrier, law, event/order boundary, arithmetic convention, and conclusion against the expanded Lean signature atom by atom. |
| The paper displays I(a\|theta) as the real supremum over z of z a minus Lambda(z\|theta). | `source_definition_rate_function_formula` | exact match; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26. Lean translation recorded; Agent check by Codex GJ18 context-free Lean translator 2026-07-26; 2026-07-26 | The judgment compares the source target's carrier, law, event/order boundary, arithmetic convention, and conclusion against the expanded Lean signature atom by atom. |
| The corrected support-safe rate is the extended-real supremum of z a minus Lambda(z\|theta), so thresholds outside finite score support may have infinite cost. | `source_definition_extended_rate_function_formula` | exact match; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26. Lean translation recorded; Agent check by Codex GJ18 context-free Lean translator 2026-07-26; 2026-07-26 | The judgment compares the source target's carrier, law, event/order boundary, arithmetic convention, and conclusion against the expanded Lean signature atom by atom. |
| Source-fidelity diagnostic, not an advertised source theorem: under the finite ordinal source primitives, positive match rates, and a nontrivial scale, the legacy unrestricted Real pairwise threshold rate is zero while the support-safe WithTop pairwise threshold rate is strictly positive. | `source_fidelity_diagnostic_unrestricted_real_pairwise_rate_mismatch` | exact match; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26. Lean translation recorded; Agent check by Codex GJ18 context-free Lean translator 2026-07-26; 2026-07-26 | The judgment compares the source target's carrier, law, event/order boundary, arithmetic convention, and conclusion against the expanded Lean signature atom by atom. |
| For every ordered high/low seller pair in the author-approved finite ordinal IID model, with positive match rates, a nontrivial rating scale, corrected ordinal tails, and an extended-real rate convention, the source-state weak-inversion probability has an exponential-rate certificate with a finite real representative of the support-safe pairwise threshold rate. | `source_appendix_problessthan_score_gap_rate_iid_completion` | exact match; approved corrected source target; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26. Lean translation recorded; Agent check by Codex GJ18 context-free Lean translator 2026-07-26; 2026-07-26 | The judgment compares each expanded Lean binder and conclusion against the explicit author-approved corrected target, retaining the archival statement as a non-equivalence baseline. |
| For every ordered high/low seller pair in the author-approved finite ordinal IID model, with positive match rates, a nontrivial rating scale, corrected ordinal tails, and an extended-real rate convention, one minus the source-state P_k objective has an exponential-rate certificate with the same finite real representative of the support-safe pairwise threshold rate. | `source_appendix_pk_ld_complement_rate_iid_completion` | exact match; approved corrected source target; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26. Lean translation recorded; Agent check by Codex GJ18 context-free Lean translator 2026-07-26; 2026-07-26 | The judgment compares each expanded Lean binder and conclusion against the explicit author-approved corrected target, retaining the archival statement as a non-equivalence baseline. |
| Corrected form of the source convergence prose: under the explicit finite IID completion, literal ordinal-tail primitives, positive match rates, and at least two rating levels, P_k for every ordered seller pair tends to one. | `source_pairwise_objective_tendsto_one_iid_completion` | exact match; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26. Lean translation recorded; Agent check by Codex GJ18 context-free Lean translator 2026-07-26; 2026-07-26 | The judgment compares the source target's carrier, law, event/order boundary, arithmetic convention, and conclusion against the expanded Lean signature atom by atom. |
| Corrected form of the source convergence prose: under the explicit finite IID completion, literal ordinal-tail primitives, positive match rates, at least two rating levels, and a nonempty adjacent seller carrier, W_k tends to one. | `source_uniform_ranking_objective_tendsto_one_iid_completion` | exact match; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26. Lean translation recorded; Agent check by Codex GJ18 context-free Lean translator 2026-07-26; 2026-07-26 | The judgment compares the source target's carrier, law, event/order boundary, arithmetic convention, and conclusion against the expanded Lean signature atom by atom. |
| Corrected Theorem 1: for the explicit finite IID completion of the finite ordinal source model, with positive match rates, at least two rating levels, and at least one adjacent seller pair, one minus the finite uniform ranking objective has the exact support-safe extended exponential rate given by the minimum adjacent threshold rate. | `source_theorem1_informative_rating_system_rate_iid_completion` | exact match; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26. Lean translation recorded; Agent check by Codex GJ18 context-free Lean translator 2026-07-26; 2026-07-26 | The judgment compares the source target's carrier, law, event/order boundary, arithmetic convention, and conclusion against the expanded Lean signature atom by atom. |
| Author-approved corrected-model Theorem 1, extended-rate form: the literal finite state-level W_k under the record's IID state law has the exact support-safe extended exponential rate given by the minimum adjacent threshold rate. | `author_confirmed_clarified_model_theorem1_state_rate` | exact match; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26. Lean translation recorded; Agent check by Codex GJ18 context-free Lean translator 2026-07-26; 2026-07-26 | The judgment compares the source target's carrier, law, event/order boundary, arithmetic convention, and conclusion against the expanded Lean signature atom by atom. |
| For the author-approved corrected finite ordinal IID model with at least two uniformly distributed seller types, positive at-most-one-per-period match rates, a nontrivial ordinal rating scale, and valid adjacent pairs 0 <= i <= M-2, one minus the state-level W_k objective has a finite real exponential rate equal to the finite representative of the support-safe adjacent-pair rate. | `author_approved_corrected_model_theorem1_finite_real_rate` | exact match; approved corrected source target; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26. Lean translation recorded; Agent check by Codex GJ18 context-free Lean translator 2026-07-26; 2026-07-26 | The judgment compares each expanded Lean binder and conclusion against the explicit author-approved corrected target, retaining the archival statement as a non-equivalence baseline. |
| - The source's ordered finite-chain match-rate and one-match schedule model. | `source_match_schedule_coherence` | additional assumption; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26 | The source explicitly gives a nondecreasing match function and at-most-one matching prose; the exact floor-step coherence and nonnegativity used by Lean are recorded through the author-approved 0 < g(theta) <= 1 correction. |
| - Source model: rating scores take values in the displayed interval `[0, 1]`. | `source_rating_scores_in_unit_interval` | source condition; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26 | The source explicitly restricts each rating score to the interval [0,1], matching the two-sided real inequality in the Lean predicate. |
| - Source model: the displayed rating score is strictly increasing. | `source_strictly_increasing_rating_scores` | additional assumption; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26 | Strict score monotonicity is invoked in the source convergence discussion and is made an explicit author-approved finite-ordinal model clause; it is not inferred from the weaker [0,1] range condition. |
| - Literal source-tail contract: for each pair of adjacent *displayed* cutoffs, the cumulative tail strictly decreases. Its index `r : Fin m` deliberately omits the terminal rating, because the source has no displayed cutoff above it. | `source_strict_ordinal_cumulative_tail_decrease_at_displayed_cutoffs` | source condition; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26 | The source says cumulative rating tails strictly decrease with rating level. Lean states that only between adjacent displayed cutoffs, avoiding an invented cutoff above the finite maximum. |
| - Author-approved corrected ordinal quality condition: a higher seller has a strictly larger upper tail at every nonbottom displayed cutoff. Strictness at cutoff zero is intentionally excluded, since that tail is always one; the pinned archive's all-cutoff wording is recorded separately as a fidelity delta. | `source_strict_ordinal_quality_tail_increase_above_bottom` | additional assumption; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26 | The archive says tails strictly increase with quality, but strictness at the bottom cutoff is impossible because that upper tail is always one. The approved correction restricts strictness to nonbottom displayed cutoffs. |
| - Sellers receive positive asymptotic match/sample rates. | `assumption_positive_match_rates` | additional assumption; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26 | Positive match rates are explicit in the author-approved corrected model so every seller's floor sample count diverges; the archive's nondecreasing-rate prose alone does not establish positivity. |
<!-- END GENERATED STATEMENT VALIDATOR LEDGER -->

## 21. Source-Coverage Audit Ledger

Four source-result clusters are covered on explicit author-approved corrected
targets. The remaining review rows expose the source definitions, premises, and
formula dependencies needed to assess those results. Archival equivalence is
not claimed.

<!-- BEGIN GENERATED SOURCE COVERAGE LEDGER -->
### Current Canonical Evidence
- Coverage scope: named theoretical statements.
- Source inventory: 11 source statements from `sources/arxiv.tex`.
- Coverage result: 4 corrected target covered, 7 no completed coverage check.
- Coverage review: coverage ledger recorded; Agent check by Codex GJ18 semantic fidelity auditor 2026-07-26; 2026-07-26.
- Row-local statement checks: 11/11 linked row references have a completed canonical statement check; repeated links are counted per source row.

| Source statement | Linked Lean review rows | Coverage judgment | Row-local statement checks | Comments |
| --- | --- | --- | --- | --- |
| Appendix Lemma problessthan: in the paper's ordered seller-pair scope theta_1 > theta_2, the weak score-gap event has the displayed real-valued rate infimum over a in R of the two sampled sellers' match-rate-weighted rate functions. | `source_appendix_problessthan_score_gap_rate_iid_completion` | corrected target covered | `source_appendix_problessthan_score_gap_rate_iid_completion`: exact match; approved corrected source target | The endpoint proves the approved corrected target under its explicit finite IID, rate, carrier, and codomain clauses. The archival statement remains a documented delta and receives no equivalence credit. |
| Appendix Lemma P_k-LD: in the paper's ordered seller-pair scope theta_1 > theta_2, Pbar_k = 1 - P_k has the displayed real-valued exponential rate equal to the same infimum of the two sellers' match-rate-weighted rate functions. | `source_appendix_pk_ld_complement_rate_iid_completion` | corrected target covered | `source_appendix_pk_ld_complement_rate_iid_completion`: exact match; approved corrected source target | The endpoint proves the approved corrected target under its explicit finite IID, rate, carrier, and codomain clauses. The archival statement remains a documented delta and receives no equivalence credit. |
| Theorem 1: the archival display sets r = -lim_k (1/k) log(1-W_k) equal to the minimum over adjacent types of the real-valued rate-function expression shown in the source. | `author_approved_corrected_model_theorem1_finite_real_rate` | corrected target covered | `author_approved_corrected_model_theorem1_finite_real_rate`: exact match; approved corrected source target | The endpoint proves the approved corrected target under its explicit finite IID, rate, carrier, and codomain clauses. The archival statement remains a documented delta and receives no equivalence credit. |
| Under the explicit finite IID completion, the source-state non-strict score-gap event equals the two-seller floor-sample weak-inversion probability used in the Appendix rate argument. | `GJ18InformativeRatingSystems.PaperInterface.source_iid_completion_weak_inversion_bridge` | no completed coverage check | `source_iid_completion_weak_inversion_bridge`: exact match | None recorded |
| Lambda(z\|theta) is the logarithm of the finite sum over rating levels of rho(theta,y\|Y) exp(z phi(y)). | `GJ18InformativeRatingSystems.PaperInterface.source_definition_log_mgf_formula` | no completed coverage check | `source_definition_log_mgf_formula`: exact match | None recorded |
| The paper displays I(a\|theta) as the real supremum over z of z a minus Lambda(z\|theta). | `GJ18InformativeRatingSystems.PaperInterface.source_definition_rate_function_formula` | no completed coverage check | `source_definition_rate_function_formula`: exact match | None recorded |
| The corrected support-safe rate is the extended-real supremum of z a minus Lambda(z\|theta), so thresholds outside finite score support may have infinite cost. | `GJ18InformativeRatingSystems.PaperInterface.source_definition_extended_rate_function_formula` | no completed coverage check | `source_definition_extended_rate_function_formula`: exact match | None recorded |
| Source-fidelity diagnostic, not an advertised source theorem: under the finite ordinal source primitives, positive match rates, and a nontrivial scale, the legacy unrestricted Real pairwise threshold rate is zero while the support-safe WithTop pairwise threshold rate is strictly positive. | `GJ18InformativeRatingSystems.PaperInterface.source_fidelity_diagnostic_unrestricted_real_pairwise_rate_mismatch` | no completed coverage check | `source_fidelity_diagnostic_unrestricted_real_pairwise_rate_mismatch`: exact match | None recorded |
| Corrected Theorem 1: for the explicit finite IID completion of the finite ordinal source model, with positive match rates, at least two rating levels, and at least one adjacent seller pair, one minus the finite uniform ranking objective has the exact support-safe extended exponential rate given by the minimum adjacent threshold rate. | `GJ18InformativeRatingSystems.PaperInterface.source_theorem1_informative_rating_system_rate_iid_completion` | no completed coverage check | `source_theorem1_informative_rating_system_rate_iid_completion`: exact match | None recorded |
| Author-approved corrected-model Theorem 1, extended-rate form: the literal finite state-level W_k under the record's IID state law has the exact support-safe extended exponential rate given by the minimum adjacent threshold rate. | `GJ18InformativeRatingSystems.PaperInterface.author_confirmed_clarified_model_theorem1_state_rate` | no completed coverage check | `author_confirmed_clarified_model_theorem1_state_rate`: exact match | None recorded |
| The archival aggregate-score display divides by n_k(theta) while summing from ell = 0 through n_k(theta), although the surrounding prose calls it the average of ratings received by time k. | `source_definition_aggregate_score_formula` | corrected target covered | `source_definition_aggregate_score_formula`: exact match; approved corrected source target | The endpoint proves the approved corrected target under its explicit finite IID, rate, carrier, and codomain clauses. The archival statement remains a documented delta and receives no equivalence credit. |
<!-- END GENERATED SOURCE COVERAGE LEDGER -->
