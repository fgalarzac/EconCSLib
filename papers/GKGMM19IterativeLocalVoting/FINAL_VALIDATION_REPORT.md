# Final Validation Report: Iterative Local Voting for Collective Decision-making in Continuous Spaces

## 1. Human Verdict
- Lean formalization status: conditional.
- Human dashboard review status: 0 human-reviewed rows.
- Model/agent statement validator status: current for the 40 non-assumption
  dashboard rows:
  35 `matches`, 5 strict `mismatch` rows accepted as
  `conditional_boundary`, 0 unresolved mismatches, 0 `uncertain`, 0 missing,
  0 stale.
- Assumption/proof-boundary validator status: current, with 2 configured rows:
  1 source paper condition and 1 approved `partial_boundary`.
- Review-surface validator status: current for 42 dashboard rows, above the LLM
  threshold of 30 but below the warning threshold of 50.
- Paper correctness verdict: not assessed.
- Final formalization verdict: conditional.  The only paper-local Lean axiom is
  the theorem-shaped SSGM boundary `assumption_ssgm_convergence_theorem`.
  Theorems 1-2 and Propositions 1-2 are derived from that theorem plus explicit
  finite-coordinate source semantics.  The current public closeout route is
  `FiniteCoordinateILVFullSampledProjectedSourceSemantics`: it keeps the sampled
  Theorem 2/Proposition 1 route, Proposition 2 source semantics, and the Theorem
  3 projected update/convergence/field/continuity/convexity obligations visible
  without an aggregate-feasibility source premise.  The proof-facing endpoint
  `proof_finiteCoordinateILVFullProjectedPaperConsequences_of_fullSampledProjectedSourceSemantics`
  proves the represented finite-coordinate consequences from that record and
  the single SSGM axiom.  Theorem 3 does not use the SSGM axiom; Lean proves a
  constrained alternative in general and the exact original `theorem3Statement`
  under the explicit full-space condition `E.solutionSpace = Set.univ`.

Current recursive source-record audit status: the source-record judge sidecar is
current for audit digest
`95b8554bfdc06bcb346443e11bdaa7cd49de7da918adedef8339c71b7cda45d9`
and reports 0 missing, stale, unresolved, or unapproved source-record fields.
The sampled source route now resolves the old active Theorem 2 and Proposition 1
noncollision/projected-update debts: `FiniteModelBILVAlgorithm1SampledTraceSource`
and `WeightedEuclideanL2ConcreteComponentSampledTraceSource` expose the sampled
selected-voter process, marginal-law alignment, bad-event measurability, raw
generation, and projection steps; Lean derives the deterministic records through
`proof_finiteModelBILVAlgorithm1PrimitiveTraceSource_of_sampledTrace` and
`proof_weightedEuclideanL2ConcreteComponentTraceSource_of_sampledTrace`.
The stricter "only SSGM remains" source-record standard is therefore met.  The
general constrained Theorem 3 exact endpoint is not claimed from a hidden
aggregate feasible-direction source record; it is documented by the Lean
alternative.  The old premise is not derivable from current C1/convexity,
projection, convergence, and directional-field hypotheses: Lean proves
`proof_singleton_solutionSpace_not_force_aggregate_feasible_direction` and the
abstract `X = {0}` counterexample
`proof_theorem3_abstract_hypotheses_do_not_imply_statement`.  Lean also proves
the constrained alternative
`proof_theorem3_finite_zero_or_no_aggregateFeasibleDirectionFormula_of_convergent_projectedUpdate`
and the full-space recovery theorem
`proof_theorem3Statement_of_fullSampledProjectedSourceSemantics_univ_solutionSpace`.

## 2. Source and Scope
- Paper: Garg, Kamble, Goel, Marn, and Munagala, "Iterative Local Voting for
  Collective Decision-making in Continuous Spaces".
- Source version: JAIR 64 (2019), 315-355, published 2019-02-18,
  DOI `10.1613/jair.1.11358`.
- Auxiliary source used for labels: arXiv:1702.07984v3.
- Lean folder: `papers/GKGMM19IterativeLocalVoting`.
- Human-facing theorem file:
  `papers/GKGMM19IterativeLocalVoting/PaperInterface.lean`.
- Proof-facing bridge file:
  `papers/GKGMM19IterativeLocalVoting/ProofInterface.lean`.
- Paper assumption file:
  `papers/GKGMM19IterativeLocalVoting/Assumptions.lean`.
- Source/subclaim map:
  `papers/GKGMM19IterativeLocalVoting/paper_statement_map.json`.
- Validator ledger:
  `papers/GKGMM19IterativeLocalVoting/VALIDATOR_LEDGER.md`.
- Machine export:
  `papers/GKGMM19IterativeLocalVoting/review_status_export.json`.

## 3. What Has Been Proven
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
  `PaperInterface.lean`.
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

## 4. Paper Assumption Provenance
| Assumption declaration | Validator judgment | Source / boundary | Premise judgments | Comments |
| --- | --- | --- | --- | --- |
| `assumption_conditions_c123` | `paper_condition` | JAIR 2019 Section 3, conditions C1-C3 | `hC : assumption_conditions_c123 E` is `source_text_model_primitive` | Bundles the stated model conditions: nonempty bounded closed convex solution space, unique ideal points, and bounded measurable density for independently drawn ideal points. |
| `assumption_ssgm_convergence_theorem` | `partial_boundary` | Future SSGM convergence theorem, not a source assumption | `hSSGM : assumption_ssgm_convergence_theorem E` is `partial_boundary` | Single approved theorem-shaped proof boundary returning `FiniteCoordinateILVSSGMConvergenceTheorems E`; endpoint consequences are derived separately. |

## 5. Statement Validator Findings
The declaration-keyed source/subclaim map and all LLM sidecars are current.
`python3 scripts/review_dashboard.py --paper GKGMM19IterativeLocalVoting --statement-precheck`
reports no missing or stale sidecars.

Rows marked strict `mismatch` with `resolution: "conditional_boundary"`:
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
restriction. This is the intended current conditional boundary, not a hidden
claim of full theorem equivalence.
Theorem 1-2 and Propositions 1-2 also name
`assumption_ssgm_convergence_theorem` as the external-library SSGM theorem
boundary.

No statement rows are currently marked `uncertain`. Theorem 3 remains a strict
`mismatch` with `resolution: "conditional_boundary"` because the exact adapter
is conditional on granular full finite-coordinate source semantics.  The
concrete `FiniteTheorem3DirectionalFieldModel` supplies the displayed field
formula, so the remaining mismatch is source-semantics/trace alignment with the
abstract paper theorem statement, not an abstract-field representation gap.

## 6. Additional Assumptions Beyond Paper
- `assumption_ssgm_convergence_theorem` is the only paper-local Lean axiom.
- It is not classified as a source assumption. It is a temporary, named,
  theorem-shaped proof boundary for the stochastic subgradient convergence
  theorem bundle.
- The result remains conditional until that theorem is proved in a shared
  stochastic approximation library and instantiated for the finite-coordinate
  ILV source model.

## 7. Proof-Strategy Deviations
- The formalization makes deterministic source semantics explicit rather than
  hiding endpoint conclusions behind an axiom. The remaining axiom supplies a
  theorem bundle consumed by theorem-specific source-semantics bridges.  The
  review surface includes the granular Theorem 3 source-semantics adapter, so
  non-SSGM obligations can be audited field-by-field.
- The source-semantics premises are stronger than the paper's prose theorem
  statements. They record deterministic finite-coordinate artifacts that are
  needed to apply the future SSGM theorem and the Theorem 3 projected-trace
  proof: norm semantics, C3/product-density data, trace semantics, target
  identification, and response bridges.
- Theorem 3 is outside the SSGM boundary, so it must not be hidden inside that
  approved axiom.  The replacement route uses a concrete finite normalized-field
  model, corrected global Algorithm 1 tail radii, selected-voter concentration,
  and explicit projection residual geometry; the interface now exposes the
  finite-dot expected raw-increment identities, normal-cone,
  residual-nonpositivity, and projected-step progress lemmas used by that route,
  along with the iid weighted-voter finite-dot concentration theorem for the
  corrected global-tail radii.  The remaining non-SSGM data is primitive
  trace/source semantics: proving that a concrete ILV instance supplies
  `FiniteTheorem3GlobalProjectedAlgorithm1TraceSource` and concrete
  field-continuity source data recorded in
  `FiniteCoordinateILVFullPrimitiveSourceSemantics`.  Lean derives the older
  deterministic trace core and the proof-facing skeletons afterward.  The
  explicit full-space bridge
  `finiteTheorem3GlobalProjectedAggregateFeasibilitySource_of_univ_solutionSpace`
  and proof-interface theorem
  `proof_theorem3_finite_directionalEquilibrium_of_convergent_projectedUpdate_univ_solutionSpace`
  show that this geometric field is automatically available for the
  unconstrained/full-space case; the general constrained case remains the
  source-record debt described above.

## 8. Library Lift Pass
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

## 9. DAG Audit
- DAG source: `papers/GKGMM19IterativeLocalVoting/DependencyDAG.tex`.
- Rendered DAG PDF: not generated in this closeout pass.
- Visual layout inspection: not completed in this closeout pass.
- The report status therefore does not claim a clean rendered DAG audit.

## 10. Conditional Results and Remaining Gaps
- Theorem 1: conditional only on `assumption_ssgm_convergence_theorem`; the
  deterministic source case certificate is constructed from the visible paper
  hypotheses.
- Theorem 2: conditional on sampled source semantics
  `Theorem2SampledSourceSemantics E` and
  `assumption_ssgm_convergence_theorem`.  Lean derives the older primitive
  deterministic trace source from the sampled selected-voter process, C3
  marginal-law alignment, bad-event measurability, raw Model B update formula,
  and projected update field.
- Proposition 1: conditional on sampled concrete component source semantics
  `Proposition1ConcreteComponentSampledSourceSemantics E` and on
  `assumption_ssgm_convergence_theorem`.  Lean derives the old deterministic
  component source record from sampled component ideals, component marginal
  laws, bad-event measurability, Algorithm 2 raw generation, and projection.
  From there it derives the weighted sample-subgradient trace, trajectory
  feasibility, SSGM step-size package, and social-objective bridge.
- Proposition 2: conditional on `Proposition2FiniteCoordinateSourceSemantics E`
  and
  `assumption_ssgm_convergence_theorem`. The non-SSGM source-semantics work is
  to construct the coordinate-wise median-set membership formula and, in finite
  coordinate models, product-box solution-space closure for coordinate updates.
  Lean derives the median carrier, product-coordinate
  replacement property, and local `L∞` response bridge from those data.  For a
  fixed supplied decomposition, Lean now has a narrower proof route that uses
  exactly those fixed-decomposition source fields rather than the global
  all-decompositions source package.
- Theorem 3: no SSGM axiom is used.  Lean proves the concrete finite
  normalized-gradient formula for the paper's directional field, derives the
  nonzero-field drift contradiction from coordinatewise convergence, proves the
  finite-dot raw-response expectation identities, proves the projection
  residual identity and nonpositivity geometry, and proves the iid weighted-voter
  concentration route used by the corrected global projected trace.  The
  strongest exact-statement adapter is
  `theorem3_statement_of_full_sampled_projected_source_semantics_univ`, which
  proves `theorem3Statement E` from sampled projected source semantics under
  `E.solutionSpace = Set.univ`.  For general constrained solution spaces Lean
  proves the constrained alternative
  `theorem3_zero_or_no_aggregate_feasible_direction_formula` instead of assuming
  the old aggregate feasible-direction field.  That old condition is not
  derivable from the current C1/convexity, projection, convergence, and
  directional-field hypotheses alone: `proof_singleton_solutionSpace_not_force_aggregate_feasible_direction`
  shows a singleton convex solution space blocks any positive feasible step
  along a nonzero aggregate direction, and
  `proof_theorem3_abstract_hypotheses_do_not_imply_statement` gives the
  one-dimensional `X = {0}` counterexample to the abstract theorem route.

## 11. Suspected Paper Issues or Inconsistencies
- Theorem 2 states `p > 0`, `q > 0` while using norm language. The Lean
  differentiability/subgradient route uses stricter convex differentiability
  hypotheses where needed.
- Appendix C.7 appears to duplicate the `(p = 1, q = inf)` label where the
  surrounding Theorem 1 case should include `(p = inf, q = 1)`.
- The paper switches between utility maximization and cost minimization. The
  Lean development makes that sign bridge explicit in the Model A and Model B
  rows.

## 12. Validation Checks
- `lake build GKGMM19IterativeLocalVoting`: passed.
- `python3 -m py_compile scripts/review_dashboard.py`: passed after the axiom
  parser update.
- Lean footprint: 23,379 lines across paper-local Lean files, including 2,723
  lines in `PaperInterface.lean`; the human review surface exposes 42 dashboard
  rows from 107 paper-interface declarations.
- JSON sidecar validation with `python3 -m json.tool`: passed for
  `lean_to_tex_llm.json`, `statement_match_llm.json`, and
  `assumption_match_llm.json`.
- Statement precheck: current 40-row non-assumption statement surface: 40 drafts
  and 40 judgments, 0 missing, 0 stale, 35 matches, 5 strict mismatches accepted
  as conditional boundaries, 0 unresolved mismatches, 0 uncertain.
- Review-surface audit: current 42-row dashboard surface; the no-paper-context
  surface audit is fresh and passes.
- Assumption precheck/export: current for the configured assumption rows; 2
  configured assumption rows, 0 missing, 0 stale, 1 `paper_condition`, 1
  `partial_boundary`, and 2 premise judgments.  The recursive source-record
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
  The approved `partial_boundary` axiom/premise remains intentional; there is
  no hidden-premise/source-record warning.

## 13. Final Verdict
Completion status: conditional.

The GKGMM formalization is closed at the sampled projected finite-coordinate
source-semantics boundary with no hidden aggregate-feasibility source premise.
The only paper-local Lean axiom is the SSGM theorem bundle.  The proof-facing
theorem
`proof_finiteCoordinateILVFullProjectedPaperConsequences_of_fullSampledProjectedSourceSemantics`
proves the represented named results from sampled projected source semantics
plus that SSGM boundary where applicable.  The remaining conditional status is
intentional: Theorem 1-2 and Propositions 1-2 still depend on the SSGM
convergence theorem, and Theorem 3's exact original statement is recovered under
the explicit full-space condition while the general constrained route is stated
as the Lean-proved constrained alternative.

## 14. Paper-Facing Statement Validator Ledger
The full generated validator ledger is stored at
`papers/GKGMM19IterativeLocalVoting/VALIDATOR_LEDGER.md`.

Summary:
- 35 statement rows: `matches`.
- 5 statement rows: strict `mismatch` with `resolution:
  "conditional_boundary"` for the conditional finite-coordinate convergence
  endpoints and Theorem 3's visible finite-coordinate/global-trace source
  premise.
- 0 statement rows: `uncertain`.
- 1 assumption row: `paper_condition`.
- 1 proof-boundary row: `partial_boundary`.

This ledger is provenance for statement-target metadata. It does not change the
human-only `human_review.reviewed_rows` counter.
