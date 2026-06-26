# Iterative Local Voting for Collective Decision-making in Continuous Spaces Formalization Notes

This is a lightweight handoff document for source-to-Lean mapping.

- Namespace: `GKGMM19IterativeLocalVoting`
- Official URL: https://www.jair.org/index.php/jair/article/view/11358
- DOI: https://doi.org/10.1613/jair.1.11358
- Auxiliary TeX source: arXiv:1702.07984v3
- Source PDF: `source.pdf`
- Local source text cache: `source.txt` generated with `mutool`

## Formalization checklist

- [x] Full named-result inventory copied to the README theorem table.
- [x] DAG graph includes all required paper-stage nodes and dependencies.
- [x] README status and remaining-assumption notes match proof artifacts.
- [ ] Post-formalization library elevation pass completed: reusable proof
      results, techniques, and primitives were moved into `EconCSLib` when
      local/low-risk, or recorded with destination modules in the final report.
- [ ] Recursive provenance audit completed with
      `python3 scripts/audit_repository.py --include-active --library-premise-audit --info-limit 0 --write-report docs/RECURSIVE_PROVENANCE_AUDIT_<date>.md`;
      all findings for this paper are resolved or explicitly recorded as
      partial/conditional boundaries.
- [ ] Final status review completed before publishing.

## Notes

- Date reviewed: 2026-06-18
- Last named convergence endpoint discharged unconditionally: none; current
  target surface is conditional.
- Outstanding assumptions / caveats:
  - Theorems 1-2 and Propositions 1-2 are conditional on the single
    theorem-shaped axiom `assumption_ssgm_convergence_theorem` in
    `Assumptions.lean`, plus the explicit finite-coordinate source model
    premise `FiniteCoordinateILVConcreteSourceModel`. Theorem 3 is now derived
    from an explicit paper-style Model B neighborhood-escape interface rather
    than from this SSGM boundary or a hidden environment-level drift field.
  - `assumption_conditions_c123` is a source model assumption; the SSGM theorem
    axiom is not a source assumption and is tracked separately as a
    partial-formalization boundary.
  - Stochastic subgradient descent / stochastic subgradient method convergence is
    the major current boundary. The chosen path is to formalize the paper-local
    definitions and finite-dimensional bridges around it, while keeping SSGM as
    one visible theorem-shaped axiom until a reusable stochastic-approximation
    theorem exists.
  - Optlib is a possible future base for convex/subgradient and deterministic
    first-order-method interfaces, but it is not pinned in the current Lake
    dependencies and would need a compatibility/port pass before use.
  - Appendix C.4 Lemma 3's candidate-gradient `Lq` norm algebra and
    finite-coordinate Frechet derivative attachment are formalized away from
    coordinate equalities.
  - The three Theorem 1 norm pairs are exposed as direct constructors for the
    source disjunction.
  - Algorithm 1's shifted step sizes now satisfy the two standard stochastic
    approximation conditions available without probability machinery:
    squared radii are summable and positive-radius partial sums diverge.
    Positive-radius non-summability is also exposed, and these are packaged as
    internal `SSGMStepSizeConditions`.
  - Algorithm 1's norm projection, projected update, projected-trajectory
    feasibility, stopping-window, and stop-condition formulas are now exposed in
    the human-facing interface.
  - Model B's finite-coordinate normalized movement formula is exposed with the
    subgradient vector supplied explicitly.
  - The sign-correct finite-coordinate Theorem 2 Model B formula is exposed:
    movement by the utility direction `-∇cost` reduces to `x - r * ∇cost` once
    Lemma 3 removes normalization.
  - Internal Model B-to-SSGM update bridges now compile, including the
    sign-correct Theorem 2 bridge from negative utility-gradient movement to a
    positive cost-gradient SSGM descent step.
  - Internal Algorithm 1/2 shape predicates now cover projection, norm-minimizing
    projection, stopping windows, finite projected SSGM updates, and
    reported-direction/noise/bias decomposition, plus a trajectory-level
    projected SSGM recurrence predicate, finite subgradient predicate, and
    feasibility preservation under projection.
  - The finite convex derivative-to-subgradient bridge is formalized, so future
    endpoint reductions can use differentiability plus convexity to supply
    `FiniteSubgradientAt`.
  - Finite `Lp` convexity is derived through mathlib `PiLp`, and Model B
    responses outside coordinate-equality bad events now assemble into projected
    sample-subgradient recurrences for sampled `Lp` costs with feasible
    projected iterates.
  - Finite-coordinate `Lp` scalar homogeneity is proved, and the sign-correct
    Theorem 2 Model B response is proved to hit the finite `Lq` radius boundary
    and therefore stay within the queried ball for nonnegative radii.
  - The bounded-density finite-union/null-transfer part of Theorem 2's
    coordinate-equality bad-event argument is formalized, including the product
    atomless base-measure instance, a.e. coordinate noncollision conclusion, and
    structured finite-coordinate C3 product-density carrier.
  - An environment-tied finite-coordinate C3 carrier now packages the future
    bridge from abstract `ConditionsC123`/C3 semantics to concrete
    product-density ideal-point data.
  - Theorem 2 still needs the paper's C3 density condition to be bridged to the
    structured product-measure bounded-density hypothesis, plus the final
    library-level SSGM convergence endpoint.
  - Under the structured finite-coordinate C3 product-density carrier, the
    a.e. Lemma 3 inputs now compile: unit Holder-dual candidate norm, sampled
    `Lp` subgradient certification, Model B normalization identity, and
    boundary-distance fact.
  - The paper-radius SSGM-input package now combines `ilvRadius` step-size
    conditions, bad-event-avoiding Model B projected sample-subgradient
    recurrence, and projected-iterate feasibility.
  - A concrete finite Model B ILV trace package over the environment trajectory
    now gives the exact paper-radius SSGM inputs once source response semantics
    supply projection, raw response, sampled ideal, and bad-event-avoidance
    data.
  - Model A local utility maximization under Definition 1 now has direct
    distance-to-ideal comparison lemmas against any feasible local candidate
    and against the query center.
  - Proof-facing endpoint-specialization corollaries now project the broad
    theorem schemas to the concrete Theorem 1 norm/model cases, Theorem 2 Model
    B conclusion, Proposition 1/2 Model A/B conclusions, and Theorem 3
    directional-equilibrium conclusion.
  - Theorem 3 now has a proof-facing coordinate-drift escape reduction:
    persistent same-sign bounded coordinate drift is the remaining stochastic
    coordinate displacement obligation. A narrower accumulated signed-coordinate
    lower-bound route now uses source-radius divergence to produce that
    displacement, a one-step signed-coordinate route telescopes per-step
    progress into the accumulated lower bound, and Lean converts coordinate
    escape into finite `L2` neighborhood escape. A still narrower
    Hoeffding-shell route now derives the expected harmonic signed-coordinate
    drift from fixed-sign coordinate drift, and an eventual Hoeffding-shell
    route derives coordinate escape from tail fluctuation control. The remaining
    source obligation is the concentration/fluctuation comparison between
    realized accumulated coordinate movement and that expected sum. Exact scalar
    and coordinate telescoping lemmas now expand tail displacement into one-step
    increments, and finite-voter expectation lemmas identify expected signed raw
    Model B coordinate increments, including their finite sums, with signed
    coordinates of `r * G(x)`. A sampled raw Hoeffding shell now exposes the
    selected-voter concentration claim and the exact actual-coordinate increment
    equality needed to use the paper's unprojected random-increment expansion.
    A projected raw Hoeffding shell now replaces exact increment equality with a
    bounded projection-slack obligation.
  - Need bounded-density small-ball/slice probability bounds.
  - Reusable one-dimensional bounded-density interval bounds now exist in
    `Foundations/Probability/BoundedDensity`, with finite-product box/slab
    bounds now available for bounded-coordinate regions.
- Reusable library elevation candidates:
  - `Foundations/Analysis/FiniteDimensionalNorms`
  - `Foundations/Optimization/Subgradient`
  - `Foundations/Probability/StochasticApproximation`
  - `Foundations/Probability/BoundedDensity`
