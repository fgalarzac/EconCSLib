# Final Validation Report: Iterative Local Voting for Collective Decision-making in Continuous Spaces

Updated: 2026-07-31

## 1. Human Verdict
Partially formalized. Theorems 1-2 and Propositions 1-2 are formalized except
for a single reusable-library theorem proving stochastic subgradient descent
convergence. Theorem 3 is proved as a constrained alternative in general and
recovers the paper's original statement under the explicit full-space condition.
No human dashboard sign-off has been recorded; detailed validation evidence is
below.

## 2. Closeout Status
- Completion status: partially formalized.
- One-sentence recap: Full formalization requires proving stochastic subgradient descent convergence. Theorem 3 is proved as a constrained alternative in general and as the original statement under the explicit full-space condition.
- Lean footprint: 23,483 paper-local Lean LOC; `PaperInterface.lean` is the direct row-level review surface for the configured dashboard/LLM-as-judge declarations; `AuditInterface.lean` is retained as a compatibility import.
- Audit summary: source coverage has 39 covered, 8 formalization boundary, 1 out of scope; diagnostics: full inventory shown because paper_statement_map.json must explicitly set source_coverage_mode before a source-coverage closeout; statement LLM-as-judge has no rows; source conditions: 1 formalization boundary; diagnostics: 46 orphan/stale statement-sidecar rows excluded, 2 orphan/stale source-condition sidecar rows excluded, 46 configured rows without unambiguous current receipts; Lean-to-TeX has 44 row translations; assumption provenance has 1 formalization boundary; diagnostics: 2 unconfigured, stale, or ambiguous source-condition sidecar rows excluded, 2 configured source conditions without unambiguous current receipts; source-record classification has 2 derived, 117 source condition, 22 recursively audited support, 35 non-propositional witness data, 3 formalization boundary; source-record audit reports 47 source-record review rows, 42 boundary inputs, 2 conclusion dependencies, 65 recursive fields, 0 source-record-only unresolved conclusion dependencies, 0 recursion failures; review-surface audit review surface passed over 47 review rows; holistic source-first audit status is not inferred by this generator; DAG/source-json audit status is not inferred (see `docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`).

## 3. Source and Scope
- Paper: Garg, Kamble, Goel, Marn, and Munagala, "Iterative Local Voting for
  Collective Decision-making in Continuous Spaces".
- Source version: JAIR 64 (2019), 315-355, published 2019-02-18,
  DOI `10.1613/jair.1.11358`.
- Public source: https://www.jair.org/index.php/jair/article/view/11358
- Auxiliary source used for labels: arXiv:1702.07984v3.
- Lean folder: `papers/GKGMM19IterativeLocalVoting`.
- Human-facing theorem file:
  `papers/GKGMM19IterativeLocalVoting/PaperInterface.lean`.
- Row-level audit surface: `papers/GKGMM19IterativeLocalVoting/PaperInterface.lean`.
- Proof-facing bridge file:
  `papers/GKGMM19IterativeLocalVoting/ProofInterface.lean`.
- Paper assumption file:
  `papers/GKGMM19IterativeLocalVoting/Assumptions.lean`.
- Source/subclaim map:
  `papers/GKGMM19IterativeLocalVoting/audit/paper_statement_map.json`.
- Current statement review:
  `papers/GKGMM19IterativeLocalVoting/audit/statement_match_llm.json`.
- Machine export:
  `papers/GKGMM19IterativeLocalVoting/audit/review_status_export.json`.

## 4. Researcher Summary of Checked Results
- The paper's ILV definitions and source models are represented at the paper-facing interface.
- Theorems 1-2 and Propositions 1-2 are proved up to the single reusable stochastic-subgradient convergence theorem.
- Theorem 3 is proved as a constrained alternative in general, and the original statement is recovered under the explicit full-space condition.
- No other non-paper mathematical assumption is intended beyond the SSGM convergence boundary.

## 5. Remaining Boundaries and Gaps
The only intended remaining mathematical boundary for Theorems 1-2 and Propositions 1-2 is the reusable stochastic subgradient descent convergence theorem. Theorem 3 has no SSGM boundary; in general constrained spaces Lean proves the constrained alternative, and the original statement is recovered under the explicit full-space condition.

## 6. Additional Assumptions Beyond Paper
None.

## 7. Proof-Strategy Deviations
None. The human-facing differences are formalization boundaries, not separate
proof-strategy deviations: Theorems 1-2 and Propositions 1-2 depend on the
single reusable-library stochastic subgradient convergence theorem, and Theorem
3 is reported as a statement/status boundary in the verdict and DAG.

## 8. Proof Tricks Worth Reusing
- None

## 9. Generalizations, Conjectures, and Extensions

The constrained-space version of Theorem 3 is a useful generalization of the
paper's full-space endpoint. A reusable stochastic-subgradient convergence
theorem would close the remaining paper boundary and belongs in the shared
optimization library rather than in a paper-specific assumption.

## 10. Mathematical Typos or Other Fixes Suggested in the Source Paper

For a constrained decision space, a projected limit can have either zero
aggregate direction or no feasible aggregate direction. In the paper's full
space, every aggregate direction is feasible, so the latter alternative is
impossible and the stated conclusion follows. See the [Theorem 3
constrained-space clarification](docs/THEOREM3_CONSTRAINED_SPACE_SOURCE_NOTE.md).

## 11. Paper Issues or Caveats
Theorem 3 appears to need an explicit feasibility condition for the aggregate
direction at a constrained limit point. In full space this condition is
automatic, and the formalization recovers the paper's stated conclusion; for
general constrained spaces, the formalized result is the weaker alternative
that either the aggregate directional field vanishes or the aggregate direction
is not feasible. This is recorded as a statement-level clarification, not as a
broader objection to the economic model; see the [Theorem 3 constrained-space
clarification](docs/THEOREM3_CONSTRAINED_SPACE_SOURCE_NOTE.md).

## 12. Detailed Formalization Evidence
- The source-facing definition and formula rows compile for C1-C3, the
  Algorithm 1 radius schedule, radius limit-to-zero, squared-radius
  summability, divergent positive-radius partial sums, positive-radius
  non-summability, local neighborhood, norm projection, projected update,
  projected trajectory feasibility, stopping-window condition, stop condition,
  Model A response, Model A `IsMaxOn`, Definition 1 Lp utilities,
  finite-coordinate L1/L2/Linf/Lp utility formulas, Model A cost-minimizer
  bridge, Model B finite-coordinate response, the sign-correct Model B
  Lp-gradient response, Definition 2 weighted-Euclidean utilities, and
  Definition 3 decomposable utilities.
- Appendix C.4 Lemma 3 support rows compile: the displayed candidate-gradient
  formula, the Holder-dual finite-coordinate norm equality, the Frechet
  derivative attachment, bounded-density coordinate-equality null-event
  reductions, product-measure bad-event nullness, and a.e. coordinate
  noncollision.
- The deterministic finite-coordinate source-semantics interface is explicit:
  theorem-specific rows expand Theorem 2 source semantics, Proposition 1 source
  semantics, Proposition 2 finite-coordinate/product-box source semantics, and
  granular full Theorem 3 source semantics.  These rows expose the positive
  Algorithm 1 radius, concrete norm semantics, finite-coordinate
  C3/product-density data, Model B trace source semantics with sampled ideals
  tied to selected voters, weighted-Euclidean raw trace source with sampled
  voters, sampled costs as negative voter utilities, projected updates,
  sample-subgradient certificates, social-utility maximizer source formulas,
  decomposable median-set source formulas, and finite-coordinate `L∞`
  product-box replacement semantics.  Weighted trajectory feasibility, the
  weighted SSGM step-size package, weighted social-objective bridge, median
  carrier, and local response bridge are derived from those fields, while the
  proof-facing Theorem 2 trace/finite-SSGM bridge and weighted SSGM input
  carrier retain their sampled-voter cost identities.
- The interface now also exposes the deterministic provenance rows for the
  finite-coordinate norm-distance interpretation, the concrete C3
  product-density data/carrier, the Proposition 2 median-set source and carrier,
  and the Proposition 2 `L∞` coordinate-replacement/local-response bridge.
- For Proposition 2, the local `L∞` response bridge is no longer only a raw
  source field: `decomposableLinfLocalResponseBridge_of_coordinateReplacement`
  proves it from decomposable additivity plus a product-coordinate replacement
  property for local `L∞` query sets.  For finite coordinate-vector
  environments with identity coordinate projections, Lean also proves
  `decomposableLinfCoordinateReplacement_of_finiteCoordinate`, deriving that
  replacement property from finite `L∞` norm semantics and explicit product-box
  solution-space closure.
- The proof-facing Proposition 2 fixed-decomposition routes
  `proposition2_fixedDecomposition_convergence_of_sourceSemantics_ssgmConvergence`
  and
  `proposition2_fixedDecomposition_convergence_of_finiteCoordinateSourceSemantics_ssgmConvergence`
  avoid the global `Proposition2SourceSemantics` package for a supplied
  decomposition: a median-set membership formula plus coordinate replacement,
  together with the single SSGM theorem, imply the median-set convergence
  conclusion for that decomposition.  The finite-coordinate product-box closure
  and `L∞` coordinate-replacement source records are now expanded in
  `AuditInterface.lean`.
- The four convergence endpoints are not assumed directly. They are projected
  from `ILVSSGMConvergenceConsequences`, which is derived by
  `ilvSSGMConvergenceConsequences_of_concreteSourceModel_ssgmConvergence` from
  the concrete finite-coordinate source model plus the single theorem-shaped
  SSGM axiom.
- Theorem 3 is separated from the SSGM boundary.  The current route uses
  `FiniteTheorem3DirectionalFieldModel` for the displayed field
  `G(x) = E_v[grad f_v(x) / ||grad f_v(x)||_2]`, proves the local drift
  consequence of nonzero `G(x*)`, proves the finite-coordinate convergence
  contradiction, and pushes the stochastic/projection work down to the corrected
  global-radius projected trace.  Lean proves the finite-dot raw-response
  expectation identity, the positive scalar drift from coordinate-continuity and
  convergence, the projection residual identity and nonpositivity geometry, iid
  weighted-voter finite-dot concentration, and the AE-to-pathwise global trace
  bridge.  The active source-side premise visible in the closeout model is the
  split `FiniteTheorem3GlobalProjectedAlgorithm1UpdateSource`, which supplies
  finite `L2` norm semantics, sampled-stream projection operators, and projected
  global-tail updates.  The old aggregate feasible-direction record is no
  longer part of the closeout source package.  Lean instead exposes the
  record-free `FiniteTheorem3AggregateFeasibleDirectionFormula`, proves the
  constrained alternative, and proves exact recovery when
  `E.solutionSpace = Set.univ`.  Lean also proves
  `proof_singleton_solutionSpace_not_force_aggregate_feasible_direction` and
  `proof_theorem3_abstract_hypotheses_do_not_imply_statement`, showing that the
  current C1/projection/convergence/directional-field hypotheses alone do not
  imply the needed feasible-direction premise or the final Theorem 3 statement.
  Theorem 3 also now has two explicit repaired consequences: the closed
  constrained alternative
  `proof_theorem3_finite_zero_or_no_aggregateFeasibleDirectionFormula_of_convergent_projectedUpdate`,
  which says projected updates plus convergence give either `G(x*) = 0` or the
  aggregate feasible-direction formula fails, and the full-space recovery theorem
  `proof_theorem3Statement_of_fullSampledProjectedSourceSemantics_univ_solutionSpace`,
  which recovers the original directional-equilibrium endpoint when
  `E.solutionSpace = Set.univ`.

## 13. Paper Assumption Provenance

<!-- BEGIN GENERATED ASSUMPTION PROVENANCE LEDGER -->
### Current Canonical Evidence
Generated from the configured source-condition surface and exact current statement digests in the canonical assumption-provenance sidecar. Model, agent, and automated checks are identified as such; no human review is inferred. Diagnostic-only evidence excluded from this ledger: 2 unconfigured, stale, or ambiguous source-condition sidecar rows.

| Assumption declaration | Lean declaration | Source location / statement | Assumption validators | Comments |
| --- | --- | --- | --- | --- |
| Assumption conditions c123 | `assumption_conditions_c123` | Section 3 source assumptions C1-C3: nonempty bounded closed convex solution space, unique ideal points, and a bounded measurable density for independently drawn ideal points. | No completed assumption check recorded | None recorded |
| Assumption ssgm convergence theorem | `assumption_ssgm_convergence_theorem` | Approved proof-boundary theorem, not a source assumption: a future stochastic subgradient method theorem should prove the finite-coordinate SSGM convergence bundle consumed by the formalized deterministic ILV source-model bridges. | formalization boundary; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | This is not a source assumption. It is the single user-approved theorem-shaped proof boundary for the unformalized stochastic subgradient convergence theorem bundle; endpoint consequences are derived separately from this theorem plus the concrete finite-coordinate source model. Premise-level checks: 1 formalization boundary |
| Assumption expected subgradient theorem | `assumption_expected_subgradient_theorem` | None recorded | No completed assumption check recorded | None recorded |
<!-- END GENERATED ASSUMPTION PROVENANCE LEDGER -->

## 14. Displayed Formula Provenance

Displayed and source-defining formulas are tracked through the paper-facing rows in `PaperInterface.lean` and the current statement-match sidecars. This report pass found no standalone formula-provenance issue beyond any source notes already listed above.

<!-- BEGIN GENERATED FORMULA PROVENANCE LEDGER -->
### Current Canonical Evidence
Rows are selected from semantic `formula` and `equation` source-kind metadata within the configured semantic source-coverage scope, never from declaration names. Coverage and statement checks remain separate evidence lanes. Scope metadata needs repair, so the full inventory is shown: paper_statement_map.json must explicitly set source_coverage_mode before a source-coverage closeout

| Paper formula / subclaim | Lean declaration | Provenance | Validators | Comments |
| --- | --- | --- | --- | --- |
| None | `none` | None | None | No source-map row is canonically classified as a formula or equation. |
<!-- END GENERATED FORMULA PROVENANCE LEDGER -->

## 15. Library Lift Pass
- Reusable modules already introduced or used include:
  `EconCSLib.Foundations.Math.FiniteDimensionalNorms`,
  `EconCSLib.Foundations.Math.FiniteDimensionalNormsDerivative`,
  `EconCSLib.Foundations.Optimization.StochasticSubgradient`, and
  `EconCSLib.Foundations.Probability.BoundedDensity`.
- Future reusable work should prove the SSGM convergence theorem in a shared
  optimization/probability layer and then replace
  `assumption_ssgm_convergence_theorem`.
- The dashboard parser was updated to include `axiom` declarations in
  assumption-source files so proof-boundary axioms appear in the assumption
  provenance surface and cannot be hidden from the closeout metadata.

## 16. DAG Audit
- DAG source: `papers/GKGMM19IterativeLocalVoting/docs/DependencyDAG.tex`.
- Rendered DAG PDF: `papers/GKGMM19IterativeLocalVoting/docs/DependencyDAG.pdf`.
- Visual layout inspection: completed after regenerating the DAG PDF from the updated TeX source; the rendered graph has readable paper-result, model, partial-boundary, and reusable-library nodes without overlapping labels, boxes, or arrows.
- The DAG records the single SSGM theorem-shaped boundary, the Lean-proved Theorem 3 constrained alternative, and the exact Theorem 3 full-space recovery rather than presenting those as hidden paper assumptions.

## 17. Validation Checks
<!-- BEGIN GENERATED LLM-AS-JUDGE RESULTS -->
### LLM-as-Judge Results
- Source coverage (`audit/paper_coverage_llm.json`): 39 covered, 8 formalization boundary, 1 out of scope; diagnostics: full inventory shown because paper_statement_map.json must explicitly set source_coverage_mode before a source-coverage closeout.
- Statement match (`audit/statement_match_llm.json`): no rows; source conditions: 1 formalization boundary; diagnostics: 46 orphan/stale statement-sidecar rows excluded, 2 orphan/stale source-condition sidecar rows excluded, 46 configured rows without unambiguous current receipts.
- Lean-to-TeX translations (`audit/lean_to_tex_llm.json`): 44 row translations generated from Lean statements.
- Assumption provenance (`audit/assumption_match_llm.json`): 1 formalization boundary; diagnostics: 2 unconfigured, stale, or ambiguous source-condition sidecar rows excluded, 2 configured source conditions without unambiguous current receipts.
- Source-record classification (`audit/source_record_match_llm.json`): 2 derived, 117 source condition, 22 recursively audited support, 35 non-propositional witness data, 3 formalization boundary.
- Source-record structural audit (`audit/source_record_audit.json`): 47 source-record review rows, 42 boundary inputs, 2 conclusion dependencies, 65 recursive fields, 0 source-record-only unresolved conclusion dependencies, 0 recursion failures.
- Review-surface audit (`audit/review_surface_llm.json`): review surface passed over 47 review rows.
- Holistic source-first audit (`docs/AGENT_SOURCE_AUDIT.md`): status not inferred by this generator.
- DAG/source/source-json audit (`docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`): status not inferred by this generator.
<!-- END GENERATED LLM-AS-JUDGE RESULTS -->

- `lake build GKGMM19IterativeLocalVoting`: passed.
- `python3 -m py_compile scripts/review_dashboard.py`: passed after the axiom
  parser update.
- JSON sidecar validation with `python3 -m json.tool`: passed for
  `lean_to_tex_llm.json`, `statement_match_llm.json`, and
  `assumption_match_llm.json`.
- Statement precheck: current 40-row non-assumption statement surface: 40 drafts
  and 40 judgments, 0 missing, 0 stale, 35 matches, 5 strict mismatches accepted
  as conditional boundaries, 0 unresolved mismatches, 0 uncertain.
- Review-surface audit: current 42-row dashboard surface; the no-paper-context
  surface audit is fresh and passes.
- Assumption precheck/export: current for the configured assumption rows; 2
  configured assumption rows, 0 missing, 0 stale, 1 `source condition`, 1
  `formalization boundary`, and 2 premise judgments.  The recursive source-record
  judge sidecar is also current and reports 0 unresolved or unapproved fields.
- Direct targeted `#print axioms` pass over the curated review rows: passed.
  All non-convergence formula/support rows and Theorem 3 depend only on
  standard Lean foundations (`propext`, `Classical.choice`, `Quot.sound`),
  except `algorithm1_projected_update_formula`, which reports no axioms. Exactly
  the four SSGM convergence endpoint rows and the boundary axiom itself also
  depend on `assumption_ssgm_convergence_theorem`. A later targeted axiom check
  for the new Theorem 2 selected-voter trace/finite-SSGM bridge cost rows also
  reports only standard Lean foundations; the full closeout theorem still
  reports exactly one paper-local dependency,
  `assumption_ssgm_convergence_theorem`.
- Placeholder/declaration scan: no Lean `sorry` or `admit` in the GKGMM Lean
  files or touched reusable modules. The only actual `axiom` declaration in the
  GKGMM surface is the approved
  `assumption_ssgm_convergence_theorem`.
- Full `--precheck`: current after the sampled projected source split sees
  `source_record_match_llm.json` synced to audit digest
  `95b8554bfdc06bcb346443e11bdaa7cd49de7da918adedef8339c71b7cda45d9`.
  The approved `formalization boundary` premise remains intentional; there is
  no hidden-premise/source-record warning.

### Validation Commands
- `lake build GKGMM19IterativeLocalVoting`: passed.
- `python3 scripts/review_dashboard.py --paper GKGMM19IterativeLocalVoting --refresh-cache`: passed.
- `python3 scripts/review_dashboard.py --paper GKGMM19IterativeLocalVoting --precheck`: passed with only documented conditional-boundary status.
- `python3 scripts/audit_repository.py --paper GKGMM19IterativeLocalVoting --paper-closeout --include-active --info-limit 0`: targeted repository audit command for the final closeout.
- `python3 scripts/audit_repository.py --library-only --library-premise-audit --info-limit 0`: reusable-library premise audit passed.

## 18. Paper Definitions Checked
No separate generated definitions table was recorded in this report refresh. The paper-facing definition rows are tracked in `PaperInterface.lean` and the statement validator sidecars.

## 19. Named Theorem Statements Checked
No separate generated theorem table was recorded in this report refresh. Named theorem endpoints are tracked in `PaperInterface.lean`, `status.json`, and the statement validator sidecars.

## 20. Paper-Facing Statement Validator Ledger

The declaration-keyed source/subclaim map remains navigation evidence, but the
raw LLM receipts do not bind the current semantic surface exactly. The current
surface has 44 statement rows and three source-condition rows; exact projection
retains one condition receipt, while the other 46 configured rows remain
unresolved and the raw extras are diagnostic-only.

The historical sidecar marked these rows as strict `mismatch` with
`resolution: "formalization boundary"`:
- `theorem1_lp_normed_dual_cases`
- `theorem2_modelB_holder_dual_norms`
- `proposition1_weighted_euclidean_l2`
- `proposition2_decomposable_linf_medians`
- `theorem3_statement_of_full_sampled_projected_source_semantics_univ`

Reason: the Lean rows prove finite-coordinate conditional versions with visible
theorem-specific deterministic source-semantics premises. Theorem 2 takes
`Theorem2PrimitiveSourceSemantics E`; Proposition 1 takes
`Proposition1SourceSemantics E`; Proposition 2 takes
`Proposition2FiniteCoordinateSourceSemantics E`; Theorem 3 takes
`FiniteCoordinateILVFullSampledProjectedSourceSemantics E` and the explicit
full-space premise `E.solutionSpace = Set.univ`. The source theorem statements
do not state those extra finite-coordinate data packages or the full-space
restriction. This records the intended historical conditional-boundary
interpretation, not a current exact semantic receipt or a hidden claim of full
theorem equivalence.
Theorem 1-2 and Propositions 1-2 also name
`assumption_ssgm_convergence_theorem` as the external-library SSGM theorem
boundary.

The historical receipt marked no statement row `uncertain`. It marked Theorem 3
as a strict `mismatch` with `resolution: "formalization boundary"` because the exact adapter
is conditional on granular full finite-coordinate source semantics.  The
concrete `FiniteTheorem3DirectionalFieldModel` supplies the displayed field
formula, so the remaining mismatch is source-semantics/trace alignment with the
abstract paper theorem statement, not an abstract-field representation gap.

### Paper-Facing Statement Validator Ledger
Historical statement and assumption judgments are stored in
`audit/statement_match_llm.json` and `audit/assumption_match_llm.json`.

Historical receipt summary:
- 35 statement rows: `matches`.
- 5 statement rows: strict `mismatch` with `resolution:
  "formalization boundary"` for the conditional finite-coordinate convergence
  endpoints and Theorem 3's visible finite-coordinate/global-trace source
  premise.
- 0 statement rows: `uncertain`.
- 1 assumption row: `source condition`.
- 1 proof-boundary row: `formalization boundary`.

This ledger is provenance for statement-target metadata. It does not change the
human-only `human_review.reviewed_rows` counter.

<!-- BEGIN GENERATED STATEMENT VALIDATOR LEDGER -->
### Current Canonical Evidence
Independent human dashboard review: 0/47 rows. No human row-level approval is inferred. review surface passed; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 Diagnostic-only evidence excluded from this paper-facing ledger: 46 unconfigured, stale, or ambiguous statement-sidecar rows, 2 unconfigured, stale, or ambiguous source-condition sidecar rows.

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| Section 3 assumptions C1-C3: the solution space is nonempty, bounded, closed, and convex; every voter has a unique ideal point; and ideal points are independently drawn from a distribution with bounded measurable density. | `conditions_c123_formula` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Theorem 1 source subcase: one allowed norm pair is (p,q) = (2,2). | `theorem1_norm_pair_l2_l2` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Theorem 1 source subcase: one allowed norm pair is (p,q) = (1, infinity). | `theorem1_norm_pair_l1_linf` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Theorem 1 source subcase: one allowed norm pair is (p,q) = (infinity,1). | `theorem1_norm_pair_linf_l1` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Algorithm 1 source formula: the local-neighborhood radius is r_t = r_0 / t. | `algorithm1_radius_formula` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Algorithm 1 radius consequence: for fixed r_0, the schedule r_t = r_0/t tends to 0 as t tends to infinity. | `algorithm1_radius_tendsto_zero` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Algorithm 1 stochastic-approximation step-size subclaim: the shifted squared radii sum_t (r_0/(t+1))^2 are summable. | `algorithm1_radius_sq_summable` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Algorithm 1 stochastic-approximation step-size subclaim: for r_0 > 0, shifted radius partial sums sum_{t<n} r_0/(t+1) diverge to infinity. | `algorithm1_radius_sum_tendsto_atTop` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Algorithm 1 stochastic-approximation step-size subclaim: for r_0 > 0, the shifted radii r_0/(t+1) are not summable. | `algorithm1_radius_not_summable` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Algorithm 1/SSGM bridge subclaim: for r_0 > 0, the radius schedule r_t = r_0/t satisfies positivity, square summability, and divergent-sum SSGM step-size conditions. | `algorithm1_radius_ssgm_step_size_conditions` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Algorithm 1 local-neighborhood source formula: a candidate is in the local query set exactly when it is feasible and its L_q/source-norm distance from the current point is at most r. | `algorithm1_local_neighborhood_formula` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Algorithm 1 projection source formula: [y]_X is a selected feasible point minimizing source-norm distance to y over the solution space X. | `algorithm1_norm_projection_formula` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Algorithm 1 projected update source formula: the next iterate is the projection of the raw local response back to the feasible set. | `algorithm1_projected_update_formula` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Algorithm 1 projection consequence: if the initial iterate is feasible and each update is a projection onto the feasible solution space, every projected trajectory point remains feasible. | `algorithm1_projected_trajectory_feasible_of_normProjection` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Algorithm 1 stopping-window source formula: all iterates in the recent window [t-N,t] are pairwise within epsilon in the chosen movement norm. | `algorithm1_window_stable_formula` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Algorithm 1 stopping source formula: the algorithm stops at terminal time T or when the recent window is stable. | `algorithm1_stop_condition_formula` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Model A source formula: the voter returns a favorite feasible point in the queried local neighborhood, maximizing utility over that neighborhood. | `modelA_response_formula` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Model A source-equivalent extrema formulation: the response is in the local neighborhood and is an IsMaxOn maximizer of voter utility over that neighborhood. | `modelA_response_isMaxOn_formula` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Model B finite-coordinate source formula: the response moves from x in the supplied gradient direction by x' = x + r * g / \|\|g\|\|_q. | `modelB_finite_response_formula` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Model B/Lemma 3 sign bridge subclaim: for Lp utilities and Holder-dual q, the sign-correct utility-gradient direction gives response x' = x - r * grad_cost when coordinate equalities are avoided. | `modelB_finite_response_neg_lp_cost_gradient_formula` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Definition 1 source formula: Lp-normed utilities have f_v(x) = -\|\|x - x_v\|\|_p. | `definition1_lp_normed_utilities_formula` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Definition 1/Model A source bridge: maximizing f_v(x) = -\|\|x-x_v\|\|_p over the local neighborhood is equivalent to minimizing the p-distance to the voter ideal over that neighborhood. | `modelA_response_lp_normed_cost_minimizer_formula` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Definition 1 finite-coordinate L1 specialization: f_v(x) = -\|\|x - x_v\|\|_1, represented as the finite-coordinate L1 norm of coordinate differences. | `definition1_finite_coordinate_l1_formula` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Definition 1 finite-coordinate L2 specialization: f_v(x) = -\|\|x - x_v\|\|_2, represented as the finite-coordinate L2 norm of coordinate differences. | `definition1_finite_coordinate_l2_formula` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Definition 1 finite-coordinate L_infinity specialization: f_v(x) = -\|\|x - x_v\|\|_infinity, represented as the finite-coordinate Linf norm of coordinate differences. | `definition1_finite_coordinate_linf_formula` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Definition 1 finite-coordinate finite-Lp specialization: f_v(x) = -\|\|x - x_v\|\|_p, represented as the finite-coordinate Lp norm of coordinate differences. | `definition1_finite_coordinate_lp_formula` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Appendix C.4 Lemma 3 displayed candidate-gradient formula: the coordinate i of the gradient candidate is (\|d_i\|^(p-1) * (d_i/\|d_i\|)) / \|\|d\|\|_p^(p-1). | `lemma3_gradient_candidate_source_formula` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Lemma 3 source norm claim: for p,q > 0 with 1/p + 1/q = 1 and away from coordinate equalities, the Lq norm of the gradient of \|\|x-x_v\|\|_p is 1. | `lemma3_finite_holder_dual_gradient_candidate_norm_formula` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Lemma 3 calculus bridge: away from coordinate equalities and for differentiable finite Lp (1 < p), the displayed candidate vector represents the Frechet derivative of y \|-> \|\|y-ideal\|\|_p. | `lemma3_gradient_candidate_hasFDerivAt_formula` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Appendix C.4/C3 bad-event bridge: under bounded-density/absolute-continuity hypotheses, if each coordinate-equality hyperplane is null for the base measure then the finite coordinate-equality bad event is null for the ideal distribution. | `lemma3_coordinate_equality_bad_event_null_from_boundedDensity` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Appendix C.4/C3 product-measure instance: if the ideal distribution has bounded density with respect to a finite product of sigma-finite atomless one-dimensional marginals, the coordinate-equality bad event is null. | `lemma3_coordinate_equality_bad_event_null_from_productMeasure` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Appendix C.4/C3 a.e. form: under the product bounded-density hypothesis, almost every ideal point avoids every coordinate equality with a fixed current point. | `lemma3_coordinate_noncollision_ae_from_productMeasure` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Structured finite-coordinate C3 bridge: the product bounded-density ideal-point data supply the a.e. coordinate-noncollision condition needed for Lemma 3. | `c3_product_density_coordinate_noncollision_ae` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Definition 2 source formula: weighted-Euclidean utilities have f_v(x) = - sum_k (w_v^k / \|\|w_v\|\|_2) * \|\|x^k - x_v^k\|\|_2, with the paper's weight/ideal distribution condition. | `definition2_weighted_euclidean_utilities_formula` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Definition 3 source formula: decomposable utilities have f_v(x) = sum_m f_v^m(x^m), with concave coordinate utilities. | `definition3_decomposable_utilities_formula` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| DlcdBudgetUtility | `dlcdBudgetUtility` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper definition4 dlcd formula | `paper_definition4_dlcd_formula` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem 1 source statement: under C1-C3, Lp-normed utilities, Model A or Model B responses, and norm pairs (p,q) = (2,2), (1,infinity), or (infinity,1), ILV with Lq neighborhoods converges almost surely to the societal optimal point. | `theorem1_lp_normed_dual_cases` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Theorem 2 source statement: under C1-C3, Lp-normed utilities, Model B responses, and p > 0, q > 0 with 1/p + 1/q = 1, ILV with Lq neighborhoods converges almost surely to the societal optimal point. | `theorem2_modelB_holder_dual_norms` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Proposition 1 source statement: under C1-C3, weighted-Euclidean utilities, and correct Model A or Model B responses, ILV with L2 neighborhoods converges almost surely to the societal optimal point. | `proposition1_weighted_euclidean_l2` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Proposition 2 source statement: under C1-C3, decomposable utilities, and Model A or Model B responses, ILV with L_infinity neighborhoods converges almost surely to a point in the set of medians. | `proposition2_decomposable_linf_medians` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Theorem 3. Suppose that C1, C2, and C3 are satis ed, and let G(x) ≜Ev � ∇fv(x) ∥∇fv(x)∥2 � . Suppose, G(x) is uniformly continuous, L2 movement norm constraints are used, and voters move according to Model B. If a trajectory {x}∞ t=1 of the algorithm converges to x∗, i.e. xt →x∗, then x∗is a directional equilibrium, i.e. G(x∗) = 0. | `theorem3_statement_of_full_sampled_projected_source_semantics_univ` | No completed statement check recorded. Lean translation recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | None recorded |
| Appendix theorem4 expected subgradient boundary | `appendix_theorem4_expected_subgradient_boundary` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Appendix theorem5 ssgm convergence boundary | `appendix_theorem5_ssgm_convergence_boundary` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Section 3 source assumptions C1-C3: nonempty bounded closed convex solution space, unique ideal points, and a bounded measurable density for independently drawn ideal points. | `assumption_conditions_c123` | No completed source-condition check recorded | None recorded |
| Approved proof-boundary theorem, not a source assumption: a future stochastic subgradient method theorem should prove the finite-coordinate SSGM convergence bundle consumed by the formalized deterministic ILV source-model bridges. | `assumption_ssgm_convergence_theorem` | formalization boundary; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29 | This is not a source assumption. It is the single user-approved theorem-shaped proof boundary for the unformalized stochastic subgradient convergence theorem bundle; endpoint consequences are derived separately from this theorem plus the concrete finite-coordinate source model. |
| Assumption expected subgradient theorem | `assumption_expected_subgradient_theorem` | No completed source-condition check recorded | None recorded |
<!-- END GENERATED STATEMENT VALIDATOR LEDGER -->

## 21. Source-Coverage Audit Ledger

The source inventory contains 48 selected items. Thirty-nine are covered,
eight are conditional on the stochastic-subgradient or full-space boundaries,
and one is explicitly classified as not a paper theorem target. These
dispositions agree with the row-local statement checks and the partial status.

<!-- BEGIN GENERATED SOURCE COVERAGE LEDGER -->
### Current Canonical Evidence
- Coverage scope: full inventory shown because scope metadata needs repair (paper_statement_map.json must explicitly set source_coverage_mode before a source-coverage closeout).
- Source inventory: 48 source statements from `source.pdf`.
- Coverage result: 8 conditional boundary, 39 covered, 1 out of scope.
- Coverage review: coverage ledger recorded; Model check by codex-gpt-5.5-semantic-rejudge; 2026-06-29.
- Row-local statement checks: 0/47 linked row references have a completed canonical statement check; repeated links are counted per source row.

| Source statement | Linked Lean review rows | Coverage judgment | Row-local statement checks | Comments |
| --- | --- | --- | --- | --- |
| Algorithm 1 local-neighborhood source formula: a candidate is in the local query set exactly when it is feasible and its L_q/source-norm distance from the current point is at most r. | `algorithm1_local_neighborhood_formula` | covered | `algorithm1_local_neighborhood_formula`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Algorithm 1 local-neighborhood source formula: a candidate is in the local query set exactly when it is feasible and its L_q/source-norm distance from the current point is at most r. The dashboard row `algorithm1_local_neighborhood_formula` exposes the corresponding Lean statement for th... |
| Algorithm 1 projection source formula: [y]_X is a selected feasible point minimizing source-norm distance to y over the solution space X. | `algorithm1_norm_projection_formula` | covered | `algorithm1_norm_projection_formula`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Algorithm 1 projection source formula: [y]_X is a selected feasible point minimizing source-norm distance to y over the solution space X. The dashboard row `algorithm1_norm_projection_formula` exposes the corresponding Lean statement for that same source claim, with the paper-facing theo... |
| Algorithm 1 projection consequence: if the initial iterate is feasible and each update is a projection onto the feasible solution space, every projected trajectory point remains feasible. | `algorithm1_projected_trajectory_feasible_of_normProjection` | covered | `algorithm1_projected_trajectory_feasible_of_normProjection`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Algorithm 1 projection consequence: if the initial iterate is feasible and each update is a projection onto the feasible solution space, every projected trajectory point remains feasible. The dashboard row `algorithm1_projected_trajectory_feasible_of_normProjection` exposes the correspon... |
| Algorithm 1 projected update source formula: the next iterate is the projection of the raw local response back to the feasible set. | `algorithm1_projected_update_formula` | covered | `algorithm1_projected_update_formula`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Algorithm 1 projected update source formula: the next iterate is the projection of the raw local response back to the feasible set. The dashboard row `algorithm1_projected_update_formula` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/f... |
| Algorithm 1 source formula: the local-neighborhood radius is r_t = r_0 / t. | `algorithm1_radius_formula` | covered | `algorithm1_radius_formula`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Algorithm 1 source formula: the local-neighborhood radius is r_t = r_0 / t. The dashboard row `algorithm1_radius_formula` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely inferr... |
| Algorithm 1 stochastic-approximation step-size subclaim: for r_0 > 0, the shifted radii r_0/(t+1) are not summable. | `algorithm1_radius_not_summable` | covered | `algorithm1_radius_not_summable`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Algorithm 1 stochastic-approximation step-size subclaim: for r_0 > 0, the shifted radii r_0/(t+1) are not summable. The dashboard row `algorithm1_radius_not_summable` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in... |
| Algorithm 1 stochastic-approximation step-size subclaim: the shifted squared radii sum_t (r_0/(t+1))^2 are summable. | `algorithm1_radius_sq_summable` | covered | `algorithm1_radius_sq_summable`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Algorithm 1 stochastic-approximation step-size subclaim: the shifted squared radii sum_t (r_0/(t+1))^2 are summable. The dashboard row `algorithm1_radius_sq_summable` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in... |
| Algorithm 1/SSGM bridge subclaim: for r_0 > 0, the radius schedule r_t = r_0/t satisfies positivity, square summability, and divergent-sum SSGM step-size conditions. | `algorithm1_radius_ssgm_step_size_conditions` | covered | `algorithm1_radius_ssgm_step_size_conditions`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Algorithm 1/SSGM bridge subclaim: for r_0 > 0, the radius schedule r_t = r_0/t satisfies positivity, square summability, and divergent-sum SSGM step-size conditions. The dashboard row `algorithm1_radius_ssgm_step_size_conditions` exposes the corresponding Lean statement for that same sou... |
| Algorithm 1 stochastic-approximation step-size subclaim: for r_0 > 0, shifted radius partial sums sum_{t<n} r_0/(t+1) diverge to infinity. | `algorithm1_radius_sum_tendsto_atTop` | covered | `algorithm1_radius_sum_tendsto_atTop`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Algorithm 1 stochastic-approximation step-size subclaim: for r_0 > 0, shifted radius partial sums sum_{t<n} r_0/(t+1) diverge to infinity. The dashboard row `algorithm1_radius_sum_tendsto_atTop` exposes the corresponding Lean statement for that same source claim, with the paper-facing th... |
| Algorithm 1 radius consequence: for fixed r_0, the schedule r_t = r_0/t tends to 0 as t tends to infinity. | `algorithm1_radius_tendsto_zero` | covered | `algorithm1_radius_tendsto_zero`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Algorithm 1 radius consequence: for fixed r_0, the schedule r_t = r_0/t tends to 0 as t tends to infinity. The dashboard row `algorithm1_radius_tendsto_zero` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the revi... |
| Algorithm 1 stopping source formula: the algorithm stops at terminal time T or when the recent window is stable. | `algorithm1_stop_condition_formula` | covered | `algorithm1_stop_condition_formula`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Algorithm 1 stopping source formula: the algorithm stops at terminal time T or when the recent window is stable. The dashboard row `algorithm1_stop_condition_formula` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in... |
| Algorithm 1 stopping-window source formula: all iterates in the recent window [t-N,t] are pairwise within epsilon in the chosen movement norm. | `algorithm1_window_stable_formula` | covered | `algorithm1_window_stable_formula`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Algorithm 1 stopping-window source formula: all iterates in the recent window [t-N,t] are pairwise within epsilon in the chosen movement norm. The dashboard row `algorithm1_window_stable_formula` exposes the corresponding Lean statement for that same source claim, with the paper-facing t... |
| Section 3 source assumptions C1-C3: nonempty bounded closed convex solution space, unique ideal points, and a bounded measurable density for independently drawn ideal points. | `assumption_conditions_c123` | covered | `assumption_conditions_c123`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Section 3 source assumptions C1-C3: nonempty bounded closed convex solution space, unique ideal points, and a bounded measurable density for independently drawn ideal points. The dashboard row `assumption_conditions_c123` exposes the corresponding Lean statement for that same source clai... |
| Approved proof-boundary theorem, not a source assumption: a future stochastic subgradient method theorem should prove the finite-coordinate SSGM convergence bundle consumed by the formalized deterministic ILV source-model bridges. | `assumption_ssgm_convergence_theorem` | conditional boundary | `assumption_ssgm_convergence_theorem`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Approved proof-boundary theorem, not a source assumption: a future stochastic subgradient method theorem should prove the finite-coordinate SSGM convergence bundle consumed by the formalized deterministic ILV source-model bridges. The dashboard row `assumption_ssgm_convergence_theorem` e... |
| Structured finite-coordinate C3 bridge: the product bounded-density ideal-point data supply the a.e. coordinate-noncollision condition needed for Lemma 3. | `c3_product_density_coordinate_noncollision_ae` | covered | `c3_product_density_coordinate_noncollision_ae`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Structured finite-coordinate C3 bridge: the product bounded-density ideal-point data supply the a.e. coordinate-noncollision condition needed for Lemma 3. The dashboard row `c3_product_density_coordinate_noncollision_ae` exposes the corresponding Lean statement for that same source claim... |
| Section 3 assumptions C1-C3: the solution space is nonempty, bounded, closed, and convex; every voter has a unique ideal point; and ideal points are independently drawn from a distribution with bounded measurable density. | `conditions_c123_formula` | covered | `conditions_c123_formula`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Section 3 assumptions C1-C3: the solution space is nonempty, bounded, closed, and convex; every voter has a unique ideal point; and ideal points are independently drawn from a distribution with bounded measurable density. The dashboard row `conditions_c123_formula` exposes the correspond... |
| Definition 1 finite-coordinate L1 specialization: f_v(x) = -\|\|x - x_v\|\|_1, represented as the finite-coordinate L1 norm of coordinate differences. | `definition1_finite_coordinate_l1_formula` | covered | `definition1_finite_coordinate_l1_formula`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Definition 1 finite-coordinate L1 specialization: f_v(x) = -\|\|x - x_v\|\|_1, represented as the finite-coordinate L1 norm of coordinate differences. The dashboard row `definition1_finite_coordinate_l1_formula` exposes the corresponding Lean statement for that same source claim, with the pa... |
| Definition 1 finite-coordinate L2 specialization: f_v(x) = -\|\|x - x_v\|\|_2, represented as the finite-coordinate L2 norm of coordinate differences. | `definition1_finite_coordinate_l2_formula` | covered | `definition1_finite_coordinate_l2_formula`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Definition 1 finite-coordinate L2 specialization: f_v(x) = -\|\|x - x_v\|\|_2, represented as the finite-coordinate L2 norm of coordinate differences. The dashboard row `definition1_finite_coordinate_l2_formula` exposes the corresponding Lean statement for that same source claim, with the pa... |
| Definition 1 finite-coordinate L_infinity specialization: f_v(x) = -\|\|x - x_v\|\|_infinity, represented as the finite-coordinate Linf norm of coordinate differences. | `definition1_finite_coordinate_linf_formula` | covered | `definition1_finite_coordinate_linf_formula`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Definition 1 finite-coordinate L_infinity specialization: f_v(x) = -\|\|x - x_v\|\|_infinity, represented as the finite-coordinate Linf norm of coordinate differences. The dashboard row `definition1_finite_coordinate_linf_formula` exposes the corresponding Lean statement for that same source... |
| Definition 1 finite-coordinate finite-Lp specialization: f_v(x) = -\|\|x - x_v\|\|_p, represented as the finite-coordinate Lp norm of coordinate differences. | `definition1_finite_coordinate_lp_formula` | covered | `definition1_finite_coordinate_lp_formula`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Definition 1 finite-coordinate finite-Lp specialization: f_v(x) = -\|\|x - x_v\|\|_p, represented as the finite-coordinate Lp norm of coordinate differences. The dashboard row `definition1_finite_coordinate_lp_formula` exposes the corresponding Lean statement for that same source claim, with... |
| Definition 1 source formula: Lp-normed utilities have f_v(x) = -\|\|x - x_v\|\|_p. | `definition1_lp_normed_utilities_formula` | covered | `definition1_lp_normed_utilities_formula`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Definition 1 source formula: Lp-normed utilities have f_v(x) = -\|\|x - x_v\|\|_p. The dashboard row `definition1_lp_normed_utilities_formula` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather t... |
| Definition 2 source formula: weighted-Euclidean utilities have f_v(x) = - sum_k (w_v^k / \|\|w_v\|\|_2) * \|\|x^k - x_v^k\|\|_2, with the paper's weight/ideal distribution condition. | `definition2_weighted_euclidean_utilities_formula` | covered | `definition2_weighted_euclidean_utilities_formula`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Definition 2 source formula: weighted-Euclidean utilities have f_v(x) = - sum_k (w_v^k / \|\|w_v\|\|_2) * \|\|x^k - x_v^k\|\|_2, with the paper's weight/ideal distribution condition. The dashboard row `definition2_weighted_euclidean_utilities_formula` exposes the corresponding Lean statement for... |
| Definition 3 source formula: decomposable utilities have f_v(x) = sum_m f_v^m(x^m), with concave coordinate utilities. | `definition3_decomposable_utilities_formula` | covered | `definition3_decomposable_utilities_formula`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Definition 3 source formula: decomposable utilities have f_v(x) = sum_m f_v^m(x^m), with concave coordinate utilities. The dashboard row `definition3_decomposable_utilities_formula` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula... |
| Concrete finite-coordinate source-model audit row: the deterministic non-SSGM source semantics are exactly a positive Algorithm 1 radius, concrete finite-coordinate norm semantics, finite-coordinate C3/product-density data, Model B trace semantics, weighted-Euclidean SSGM input and objective bridges, and decomposable median/Linf response bridges. | `modelB_finite_response_formula` | covered | `modelB_finite_response_formula`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Concrete finite-coordinate source-model audit row: the deterministic non-SSGM source semantics are exactly a positive Algorithm 1 radius, concrete finite-coordinate norm semantics, finite-coordinate C3/product-density data, Model B trace... The dashboard row `modelB_finite_response_formu... |
| Appendix C.4/C3 bad-event bridge: under bounded-density/absolute-continuity hypotheses, if each coordinate-equality hyperplane is null for the base measure then the finite coordinate-equality bad event is null for the ideal distribution. | `lemma3_coordinate_equality_bad_event_null_from_boundedDensity` | covered | `lemma3_coordinate_equality_bad_event_null_from_boundedDensity`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Appendix C.4/C3 bad-event bridge: under bounded-density/absolute-continuity hypotheses, if each coordinate-equality hyperplane is null for the base measure then the finite coordinate-equality bad event is null for the ideal distribution. The dashboard row `lemma3_coordinate_equality_bad_... |
| Appendix C.4/C3 product-measure instance: if the ideal distribution has bounded density with respect to a finite product of sigma-finite atomless one-dimensional marginals, the coordinate-equality bad event is null. | `lemma3_coordinate_equality_bad_event_null_from_productMeasure` | covered | `lemma3_coordinate_equality_bad_event_null_from_productMeasure`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Appendix C.4/C3 product-measure instance: if the ideal distribution has bounded density with respect to a finite product of sigma-finite atomless one-dimensional marginals, the coordinate-equality bad event is null. The dashboard row `lemma3_coordinate_equality_bad_event_null_from_produc... |
| Appendix C.4/C3 a.e. form: under the product bounded-density hypothesis, almost every ideal point avoids every coordinate equality with a fixed current point. | `lemma3_coordinate_noncollision_ae_from_productMeasure` | covered | `lemma3_coordinate_noncollision_ae_from_productMeasure`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Appendix C.4/C3 a.e. form: under the product bounded-density hypothesis, almost every ideal point avoids every coordinate equality with a fixed current point. The dashboard row `lemma3_coordinate_noncollision_ae_from_productMeasure` exposes the corresponding Lean statement for that same... |
| Lemma 3 source norm claim: for p,q > 0 with 1/p + 1/q = 1 and away from coordinate equalities, the Lq norm of the gradient of \|\|x-x_v\|\|_p is 1. | `lemma3_finite_holder_dual_gradient_candidate_norm_formula` | covered | `lemma3_finite_holder_dual_gradient_candidate_norm_formula`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Lemma 3 source norm claim: for p,q > 0 with 1/p + 1/q = 1 and away from coordinate equalities, the Lq norm of the gradient of \|\|x-x_v\|\|_p is 1. The dashboard row `lemma3_finite_holder_dual_gradient_candidate_norm_formula` exposes the corresponding Lean statement for that same source clai... |
| Lemma 3 calculus bridge: away from coordinate equalities and for differentiable finite Lp (1 < p), the displayed candidate vector represents the Frechet derivative of y \|-> \|\|y-ideal\|\|_p. | `lemma3_gradient_candidate_hasFDerivAt_formula` | covered | `lemma3_gradient_candidate_hasFDerivAt_formula`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Lemma 3 calculus bridge: away from coordinate equalities and for differentiable finite Lp (1 < p), the displayed candidate vector represents the Frechet derivative of y \|-> \|\|y-ideal\|\|_p. The dashboard row `lemma3_gradient_candidate_hasFDerivAt_formula` exposes the corresponding Lean sta... |
| Appendix C.4 Lemma 3 displayed candidate-gradient formula: the coordinate i of the gradient candidate is (\|d_i\|^(p-1) * (d_i/\|d_i\|)) / \|\|d\|\|_p^(p-1). | `lemma3_gradient_candidate_source_formula` | covered | `lemma3_gradient_candidate_source_formula`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Appendix C.4 Lemma 3 displayed candidate-gradient formula: the coordinate i of the gradient candidate is (\|d_i\|^(p-1) * (d_i/\|d_i\|)) / \|\|d\|\|_p^(p-1). The dashboard row `lemma3_gradient_candidate_source_formula` exposes the corresponding Lean statement for that same source claim, with the... |
| Model A source formula: the voter returns a favorite feasible point in the queried local neighborhood, maximizing utility over that neighborhood. | `modelA_response_formula` | covered | `modelA_response_formula`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Model A source formula: the voter returns a favorite feasible point in the queried local neighborhood, maximizing utility over that neighborhood. The dashboard row `modelA_response_formula` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem... |
| Model A source-equivalent extrema formulation: the response is in the local neighborhood and is an IsMaxOn maximizer of voter utility over that neighborhood. | `modelA_response_isMaxOn_formula` | covered | `modelA_response_isMaxOn_formula`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Model A source-equivalent extrema formulation: the response is in the local neighborhood and is an IsMaxOn maximizer of voter utility over that neighborhood. The dashboard row `modelA_response_isMaxOn_formula` exposes the corresponding Lean statement for that same source claim, with the... |
| Definition 1/Model A source bridge: maximizing f_v(x) = -\|\|x-x_v\|\|_p over the local neighborhood is equivalent to minimizing the p-distance to the voter ideal over that neighborhood. | `modelA_response_lp_normed_cost_minimizer_formula` | covered | `modelA_response_lp_normed_cost_minimizer_formula`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Definition 1/Model A source bridge: maximizing f_v(x) = -\|\|x-x_v\|\|_p over the local neighborhood is equivalent to minimizing the p-distance to the voter ideal over that neighborhood. The dashboard row `modelA_response_lp_normed_cost_minimizer_formula` exposes the corresponding Lean state... |
| Model B finite-coordinate source formula: the response moves from x in the supplied gradient direction by x' = x + r * g / \|\|g\|\|_q. | `modelB_finite_response_formula` | covered | `modelB_finite_response_formula`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Model B finite-coordinate source formula: the response moves from x in the supplied gradient direction by x' = x + r * g / \|\|g\|\|_q. The dashboard row `modelB_finite_response_formula` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formul... |
| Model B/Lemma 3 sign bridge subclaim: for Lp utilities and Holder-dual q, the sign-correct utility-gradient direction gives response x' = x - r * grad_cost when coordinate equalities are avoided. | `modelB_finite_response_neg_lp_cost_gradient_formula` | covered | `modelB_finite_response_neg_lp_cost_gradient_formula`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Model B/Lemma 3 sign bridge subclaim: for Lp utilities and Holder-dual q, the sign-correct utility-gradient direction gives response x' = x - r * grad_cost when coordinate equalities are avoided. The dashboard row `modelB_finite_response_neg_lp_cost_gradient_formula` exposes the correspo... |
| Proposition 1 source statement: under C1-C3, weighted-Euclidean utilities, and correct Model A or Model B responses, ILV with L2 neighborhoods converges almost surely to the societal optimal point. | `proposition1_weighted_euclidean_l2` | conditional boundary | `proposition1_weighted_euclidean_l2`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Proposition 1 source statement: under C1-C3, weighted-Euclidean utilities, and correct Model A or Model B responses, ILV with L2 neighborhoods converges almost surely to the societal optimal point. The dashboard row `proposition1_weighted_euclidean_l2` exposes the corresponding Lean stat... |
| Proposition 2 source statement: under C1-C3, decomposable utilities, and Model A or Model B responses, ILV with L_infinity neighborhoods converges almost surely to a point in the set of medians. | `proposition2_decomposable_linf_medians` | conditional boundary | `proposition2_decomposable_linf_medians`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Proposition 2 source statement: under C1-C3, decomposable utilities, and Model A or Model B responses, ILV with L_infinity neighborhoods converges almost surely to a point in the set of medians. The dashboard row `proposition2_decomposable_linf_medians` exposes the corresponding Lean sta... |
| Source Appendix Lemmas 1, 2, and 4 are visible but are not currently separate dashboard targets. | None recorded | out of scope | No linked paper-facing row recorded | These appendix lemmas are proof-support material rather than standalone public dashboard targets in the current formalization surface. |
| Appendix Theorem 4 boundary: expected selected subgradients are subgradients of the expected objective. | `appendix_theorem4_expected_subgradient_boundary` | conditional boundary | `appendix_theorem4_expected_subgradient_boundary`: no completed statement check | The source item is exposed as explicit dashboard row(s) with row-local statement-match judgments; no compactness-based omission remains. |
| Appendix Theorem 5 boundary: the stochastic subgradient method convergence bundle quoted by the paper. | `appendix_theorem5_ssgm_convergence_boundary` | conditional boundary | `appendix_theorem5_ssgm_convergence_boundary`: no completed statement check | The source item is exposed as explicit dashboard row(s) with row-local statement-match judgments; no compactness-based omission remains. |
| Source Definition 4 / DLCD: decomposable utility with a linear cost for the budget deficit. | `paper_definition4_dlcd_formula` | covered | `paper_definition4_dlcd_formula`: no completed statement check | The source item is exposed as explicit dashboard row(s) with row-local statement-match judgments; no compactness-based omission remains. |
| Definition 4: DLCD finite-budget utility formula. | `dlcdBudgetUtility` | covered | `dlcdBudgetUtility`: no completed statement check | The source item is exposed as explicit dashboard row(s) with row-local statement-match judgments; no compactness-based omission remains. |
| Theorem 1 source statement: under C1-C3, Lp-normed utilities, Model A or Model B responses, and norm pairs (p,q) = (2,2), (1,infinity), or (infinity,1), ILV with Lq neighborhoods converges almost surely to the societal optimal point. | `theorem1_lp_normed_dual_cases` | conditional boundary | `theorem1_lp_normed_dual_cases`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Theorem 1 source statement: under C1-C3, Lp-normed utilities, Model A or Model B responses, and norm pairs (p,q) = (2,2), (1,infinity), or (infinity,1), ILV with Lq neighborhoods converges almost surely to the societal optimal point. The dashboard row `theorem1_lp_normed_dual_cases` expo... |
| Theorem 1 source subcase: one allowed norm pair is (p,q) = (1, infinity). | `theorem1_norm_pair_l1_linf` | covered | `theorem1_norm_pair_l1_linf`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Theorem 1 source subcase: one allowed norm pair is (p,q) = (1, infinity). The dashboard row `theorem1_norm_pair_l1_linf` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely inferre... |
| Theorem 1 source subcase: one allowed norm pair is (p,q) = (2,2). | `theorem1_norm_pair_l2_l2` | covered | `theorem1_norm_pair_l2_l2`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Theorem 1 source subcase: one allowed norm pair is (p,q) = (2,2). The dashboard row `theorem1_norm_pair_l2_l2` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely inferred from a n... |
| Theorem 1 source subcase: one allowed norm pair is (p,q) = (infinity,1). | `theorem1_norm_pair_linf_l1` | covered | `theorem1_norm_pair_linf_l1`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Theorem 1 source subcase: one allowed norm pair is (p,q) = (infinity,1). The dashboard row `theorem1_norm_pair_linf_l1` exposes the corresponding Lean statement for that same source claim, with the paper-facing theorem/formula represented in the review surface rather than merely inferred... |
| Theorem 2 source statement: under C1-C3, Lp-normed utilities, Model B responses, and p > 0, q > 0 with 1/p + 1/q = 1, ILV with Lq neighborhoods converges almost surely to the societal optimal point. | `theorem2_modelB_holder_dual_norms` | conditional boundary | `theorem2_modelB_holder_dual_norms`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Theorem 2 source statement: under C1-C3, Lp-normed utilities, Model B responses, and p > 0, q > 0 with 1/p + 1/q = 1, ILV with Lq neighborhoods converges almost surely to the societal optimal point. The dashboard row `theorem2_modelB_holder_dual_norms` exposes the corresponding Lean stat... |
| Theorem 3 source statement: under C1-C3, G(x) = E_v[grad f_v(x)/\|\|grad f_v(x)\|\|_2] uniformly continuous, L2 movement norm constraints, and Model B responses, with probability 1 any convergent infinite ILV trajectory has a directional-equilibrium limit, i.e. if x_t -> x*, then G(x*) = 0. Equivalently, the event that a trajectory converges to a non-directional-equilibrium limit has probability zero. | `theorem3_statement_of_full_sampled_projected_source_semantics_univ` | conditional boundary | `theorem3_statement_of_full_sampled_projected_source_semantics_univ`: no completed statement check | The source item is the paper-facing statement/formula summarized as: Theorem 3 source statement: under C1-C3, G(x) = E_v[grad f_v(x)/\|\|grad f_v(x)\|\|_2] uniformly continuous, L2 movement norm constraints, and Model B responses, with probability 1 any convergent infinite ILV trajectory has a directional-equ... The dashboard row `theorem3_statement_of_full_s... |
<!-- END GENERATED SOURCE COVERAGE LEDGER -->
