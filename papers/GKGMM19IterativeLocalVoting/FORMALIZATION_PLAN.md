# Formalization Plan: Iterative Local Voting for Collective Decision-making in Continuous Spaces

This is a working scratchpad for outside-Lean proof thinking. Keep it short and
useful; it is not the final validation report.

Current note (2026-06-26): read `README.md` and
`FINAL_VALIDATION_REPORT.md` for the current authoritative status before using
older source-model notes in this scratchpad.

- Namespace: `GKGMM19IterativeLocalVoting`

## Initial Outside-Lean Paper Audit

- Source version / local files inspected:
  - JAIR article page: https://www.jair.org/index.php/jair/article/view/11358
  - JAIR PDF: `source.pdf`, 41 pages, Journal of Artificial Intelligence
    Research 64 (2019), 315-355, DOI `10.1613/jair.1.11358`.
  - Extracted text cache: `source.txt`, generated with `mutool`.
  - Auxiliary TeX source for labels and exact source snippets:
    arXiv:1702.07984v3, last revised 2018-10-28.
- Formula sanity check:
  - Algorithm 1 uses radius `r_t = r_0 / t` for `t >= 1` and projects the
    reported point to `X`.
  - Model A is exact local maximization over an Lq ball.
  - Model B moves to the Lq-boundary in a subgradient/gradient direction.
  - The paper flips between utilities `f_v(x) = -||x-x_v||_p` and costs
    `f_v(x) = ||x-x_v||_p` in the appendix; Lean should keep a sign-explicit
    utility layer and a separate cost/minimization layer before proving
    convergence.
  - Theorem 2 states finite `p,q > 0` with `1/p + 1/q = 1`; the source text
    calls these Lp/Lq norms, but true norm properties normally require
    `p,q >= 1`. This should be checked before a strong statement match.
  - The appendix's Lemma 2 final displayed case is labeled `(p = 1, q = inf)`
    again where the surrounding theorem case is `(p = inf, q = 1)`. Treat this
    as a likely source typo and verify against the TeX/source proof.
  - Formula-bearing displayed claims needing real derivations include the
    weighted-Euclidean gradient norm, the Lp/Lq gradient norm lemma, bad-region
    probability bounds, SSGM conditions, and the Theorem 3 Hoeffding/drift
    argument.
- Named result sanity check:
  - Results inventoried from the JAIR text and arXiv TeX:
    Definition 1, Definition 2, Definition 3, Theorems 1-3, Propositions 1-2,
    appendix Theorems 4-5, Lemmas 1-4.
  - Theorem 4 and Theorem 5 are imported literature theorems, not original
    paper endpoints. They should become library boundaries or imported Mathlib/
    EconCSLib lemmas, not paper-facing final results.
  - Theorem 3 is conditional: if the trajectory converges, then the limit is a
    directional equilibrium. It does not itself prove convergence.
  - No named convergence endpoint has been discharged unconditionally. The
    current Lean layer now proves substantial deterministic infrastructure:
    Lemma 3 finite-coordinate calculus, bounded-density bad-event reductions,
    projection and recurrence invariants, Model B-to-sample-SSGM bridges, and
    endpoint-specialization corollaries. The named theorem endpoints remain
    conditional wrappers around an explicit proof-boundary assumption.
- Proof strategy consequences:
  - The first pass should formalize the source vocabulary and theorem targets,
    then split the work into a reusable stochastic approximation library track
    and a paper-specific utility-response track.
  - Major unformalized library seam: finite-dimensional normed real vector
    analysis with subgradients, projections to closed convex sets, stochastic
    subgradient convergence almost surely, and bounded-density small-region
    probability bounds.
  - Major paper-specific seam: proving Model A local maximization equals the
    relevant subgradient update outside small bad regions for the three
    Theorem 1 norm pairs and weighted-Euclidean utilities.
  - No issue has yet been escalated to the user except that the current Lean
    endpoints are intentionally conditional.

## Source Inventory

- Definitions / formatted paper objects:
  - C1: `X subset R^M` is nonempty, bounded, closed, and convex.
  - C2: each voter has a unique ideal solution `x_v in X`.
  - C3: ideal points are independently drawn from a distribution with bounded
    measurable density `h_X`.
  - Algorithm 1: ILV with local Lq-ball query, radius `r_t = r_0/t`, projection
    to `X`, and a stopping condition.
  - Model A: voter exactly maximizes utility over the local Lq ball.
  - Model B: voter moves in a gradient/subgradient direction to the Lq boundary.
  - Definition 1: Lp-normed utilities, `f_v(x) = -||x-x_v||_p`.
  - Definition 2: weighted-Euclidean utilities,
    `f_v(x) = -sum_k (w_v^k / ||w_v||_2) ||x^k-x_v^k||_2`.
  - Definition 3: decomposable utilities,
    `f_v(x) = sum_m f_v^m(x^m)` with concave coordinate utilities.
  - Directional field: `G(x) = E_v[nabla f_v(x) / ||nabla f_v(x)||_2]`.
- Named lemmas / propositions / theorems / corollaries:
  - Theorem 1: Lp utilities, Model A or B, norm pairs `(2,2)`, `(1,inf)`,
    `(inf,1)` converge w.p. 1 to the societal optimum.
  - Theorem 2: Lp utilities, Model B, finite Holder-dual `p,q > 0` converge
    w.p. 1 to the societal optimum.
  - Proposition 1: weighted-Euclidean utilities, L2 neighborhoods, Model A or B
    converge w.p. 1 to the societal optimum.
  - Proposition 2: decomposable utilities, Linf neighborhoods, Model A or B
    converge w.p. 1 to the median set.
  - Theorem 3: a convergent Model B/L2 trajectory converges to a directional
    equilibrium.
  - Theorem 4: expected subgradient theorem from Nemirovski et al./Strassen.
  - Theorem 5: stochastic subgradient convergence theorem from Jiang-Walrand.
  - Lemma 1: bounded gap between reported movement direction and subgradient.
  - Lemma 2: bad-region probability is `O(r_t)` for the Theorem 1 norm pairs.
  - Lemma 3: finite Holder-dual Lp gradient has Lq norm 1 off coordinate
    equalities.
  - Lemma 4: weighted-Euclidean bad-region probability is `O(r_t)`.
- Theorem-like displayed claims that are used later:
  - `tilde_g = (x_t - argmin_x[f_vt(x) : ||x-x_t||_q <= r_t]) / r_t`.
  - Model B update `tilde_g = g_vt / ||g_vt||_q`.
  - Bias/noise decomposition
    `tilde_g_vt(x_t) = bar_g_t + z_t + b_t`.
  - Theorem 3 drift claim: if `G_m` keeps one sign and magnitude in a
    neighborhood, the trajectory leaves smaller neighborhoods w.p. 1.

## Initial Proof Strategy

- Shared-library reuse checkpoint:
  - Searched `EconCSLib/Foundations/Optimization`, including `Argmax`,
    `ChoiceEquilibriumAE`, and `StrategicEquilibrium`. These provide abstract
    choice/equilibrium interfaces, but not stochastic approximation or
    subgradient convergence.
  - Searched `EconCSLib/Foundations/Probability`, including real-distribution,
    measure-inequality, Markov-chain, and finite-expectation modules. These are
    useful for future density/probability lemmas but do not currently provide
    the almost-sure SSGM theorem or continuous small-ball/slice bounds needed
    here.
  - Checked the active Lake dependency set: this repo currently pins mathlib and
    cslib, but not Optlib. Archived repo notes identify `optsuite/optlib` as an
    optimization-library lead with convex, subgradient, KKT/Farkas, weak-duality,
    and first-order-method convergence material, but at an older Lean toolchain.
    Do not use Optlib as an implicit dependency for this paper without an
    explicit compatibility/port decision.
  - Searched social-choice ranking modules. They are finite ranking/ordinal
    infrastructure and do not fit this continuous alternative-space setting.
- Main theorem chain:
  - Definitions/C1-C3 feed Algorithm 2's SSGM restatement.
  - Theorems 4-5 provide the stochastic approximation bridge.
  - Lemmas 1-2 discharge Theorem 1 for three norm pairs.
  - Lemma 3 discharges Theorem 2 under Model B.
  - Lemma 4 discharges Proposition 1.
  - Proposition 2 reduces coordinate-wise to the Theorem 1 `(p=1,q=inf)` route.
  - Theorem 3 is separate: convergence plus continuity/drift implies directional
    equilibrium.
- Likely reusable `EconCSLib` seams:
  - `EconCSLib/Foundations/Analysis/FiniteDimensionalNorms.lean` or similar:
    Lp/Linf finite vectors, dual norm cases, gradient norm lemmas.
  - `EconCSLib/Foundations/Optimization/Subgradient.lean`: convex functions,
    subgradients, projections, optimality conditions.
  - `EconCSLib/Foundations/Probability/StochasticApproximation.lean`: SSGM
    theorem, martingale/noise conditions, almost-sure convergence.
  - `EconCSLib/Foundations/Probability/BoundedDensity.lean`: small ball/slice
    mass bounds for bounded densities on finite-dimensional spaces.
- Paper steps that look underspecified or analytically hard:
  - Theorem 5 is quoted for gradients, with an informal note that subgradients
    follow by the same proof.
  - The proof of Proposition 1 says "similar to Theorem 1"; this hides the full
    SSGM condition verification.
  - Proposition 2 gives only a proof sketch.
  - Theorem 3 uses a Hoeffding inequality over a path constrained to remain in a
    neighborhood; this likely needs careful adapted-process formulation.
- Planned fallback route if the source proof is too informal:
  - Keep the current paper-facing endpoints conditional on named analytic
    boundaries while fully formalizing the definitional layer and any elementary
    finite-vector utility lemmas that are low risk.
  - Promote reusable analysis/probability boundaries into dedicated library
    modules before removing theorem boundary assumptions.

## SSGD / Optlib Strategy Decision

- Current paper-verification path:
  - Treat stochastic subgradient descent / stochastic subgradient method
    convergence as the major named analytic boundary for this paper.
  - Fully formalize the paper-local source layer around it: C1-C3, Algorithm 1,
    local neighborhoods, Model A/Model B response formulas, finite-coordinate
    Lp/Lq norm formulas, Holder-dual algebra, utility/cost sign bridges,
    bad-region statement shapes, and theorem-shaped conditional interfaces for
    all named endpoints.
  - Make the boundary visible in `Assumptions.lean`, `status.json`,
    `FINAL_VALIDATION_REPORT.md`, and the README so human reviewers do not read
    the theorem rows as completed stochastic convergence proofs.
  - Keep exactly one paper-local theorem-boundary axiom,
    `assumption_ssgm_convergence_theorem`, whose type is the theorem-shaped
    `FiniteCoordinateILVSSGMConvergenceTheorems E`.  Source C1-C3 and the
    concrete finite-coordinate source semantics remain separate model data.
- Future library path:
  - Inspect and, if compatible, port the narrow Optlib convex-analysis and
    deterministic subgradient interfaces needed here instead of recreating them
    paper-locally.
  - Build a new EconCSLib stochastic-approximation layer on top of mathlib
    probability/process primitives and any Optlib-compatible subgradient API.
  - Only after that layer proves the Jiang-Walrand/Nemirovski-style SSGM theorem
    in the required finite-dimensional machine model should
    `assumption_ssgm_convergence_theorem` be discharged.

## Current Non-SSGM Completion Plan

As of 2026-06-26, the Lean build passes and the only intended Lean axiom remains
`assumption_ssgm_convergence_theorem`.  The recursive source-record audit is
still the controlling check.  The current `source_record_match_llm.json` is
synced to audit digest
`95b8554bfdc06bcb346443e11bdaa7cd49de7da918adedef8339c71b7cda45d9`
and reports no missing, stale, unresolved, or unapproved fields.  The sampled
projected source route
`FiniteCoordinateILVFullSampledProjectedSourceSemantics` now derives the old deterministic
Theorem 2 coordinate noncollision, Proposition 1 component noncollision, and
Proposition 1 expanded projected-update fields from sampled-process marginal
laws, bad-event measurability, raw generation, and projection semantics.  The
general constrained Theorem 3 exact endpoint is not hidden as a source
assumption; Lean proves the constrained alternative and exact full-space
recovery described below.

Resolved by the sampled route:

- `FiniteModelBILVAlgorithm1PrimitiveTraceSource.coordinate_noncollision` is
  derived by
  `proof_finiteModelBILVAlgorithm1PrimitiveTraceSource_of_sampledTrace` from
  `FiniteModelBILVAlgorithm1SampledTraceSource`.
- `WeightedEuclideanL2ConcreteComponentTraceSource.component_noncollision` and
  `WeightedEuclideanL2ConcreteComponentTraceSource.projected_update` are derived
  by `proof_weightedEuclideanL2ConcreteComponentTraceSource_of_sampledTrace`
  from `WeightedEuclideanL2ConcreteComponentSampledTraceSource`.

Remaining:

1. SSGM convergence theorem.
   - Current state: intentionally represented by the single theorem-shaped
     boundary `assumption_ssgm_convergence_theorem`.
   - What Lean now proves around it: Theorems 1-2 and Propositions 1-2 consume
     only the extracted `FiniteCoordinateILVSSGMConvergenceTheorems E` bundle;
     all deterministic/source-semantics obligations feeding that bundle are
     explicit and recursively audited.
   - Remaining work: replace the axiom with a library theorem, likely in a
     reusable optimization/probability layer.

2. Optional stronger general-constrained Theorem 3 theorem.
   - Current state: not part of the no-hidden-premise closeout.  The closeout
     proves `theorem3_zero_or_no_aggregate_feasible_direction_formula` for
     general constrained spaces and
     `theorem3_statement_of_full_sampled_projected_source_semantics_univ` for
     full-space solution sets.
   - What Lean now proves: the old aggregate feasible-direction condition is
     not derivable from the current C1/convexity, projection, convergence, and
     directional-field hypotheses alone.  A 1D example with `X = {0}`, constant
     projected trajectory, and nonzero gradient satisfies those abstract
     ingredients while falsifying any positive feasible step.
   - Remaining work if someone wants the exact general constrained endpoint:
     add and validate a stronger geometric assumption from the source model, or
     prove a stronger primitive source model implies the aggregate
     feasible-direction formula.

## Active Scratchpad

- Current Lean endpoint:
  - `lake build GKGMM19IterativeLocalVoting` succeeds.
  - The last full generated `#print axioms` pass covered the previous curated
    paper-facing rows and succeeded with only standard foundations
    (`propext`, `Classical.choice`, `Quot.sound`) outside the single SSGM
    boundary. The interface has since gained deterministic provenance rows for
    Theorem 2 selected-voter trace costs, finite-coordinate norm/C3 carriers,
    Proposition 2 source carriers, Theorem 3 finite-dot expectation identities,
    and Theorem 3 projection-residual geometry;
    it also exposes the iid weighted-voter finite-dot concentration row for the
    corrected global-tail radii;
    targeted `#print axioms` checks for the
    new selected-voter cost rows use only standard Lean foundations, and the
    full closeout theorem still reports exactly the single paper-local SSGM
    axiom. The full repository audit report
    `docs/RECURSIVE_PROVENANCE_AUDIT_GKGMM19_2026-06-18.md` was regenerated,
    but the repo-wide audit still exits nonzero on unrelated pre-existing
    papers/libraries and does not treat the untracked GKGMM folder as a
    canonical tracked paper.
  - `PaperInterface.lean` exposes C1-C3, the three Theorem 1 norm-pair cases,
    Algorithm 1 radius/local-neighborhood/projection/update/stopping formulas,
    projected-trajectory feasibility, shifted Algorithm 1 step-size
    square-summability, harmonic-divergence, non-summability, and packaged SSGM
    step-size facts, Model A response as utility maximization and mathlib
    `IsMaxOn`, the finite-coordinate Model B normalized movement formula, the
    sign-correct Theorem 2 `x - r * ∇cost` Model B formula, the Definition 1
    utility/cost-minimizer sign bridge, concrete finite-coordinate
    L1/L2/Linf/finite-Lp formulas, Appendix C.4 Lemma 3's Holder-dual
    candidate-gradient norm algebra, derivative attachment, bounded-density
    finite-union bad-event reduction, product atomless base-measure nullness,
    a.e. coordinate noncollision, and a structured finite-coordinate C3
    product-density carrier, Definitions 2-3, conditional wrappers for
    Theorems 1-2 and Propositions 1-2, and the deterministic Theorem 3 wrapper.
  - `EconCSLib.Foundations.Math.FiniteDimensionalNorms` now has source-facing
    finite-coordinate norm formulas plus bridges to mathlib `PiLp` norms for
    L1, L2, Linf, and positive finite `ENNReal` exponents. It also has
    nonnegativity, zero/self-distance, and nonzero-vector positivity lemmas for
    the L1, L2, and finite-Lp formulas now used by the GKGMM19 finite-coordinate
    wrappers.
  - Theorem 1 and Proposition 2 now also have theorem-shaped SSGM
    case-certificate interfaces, complementing the Theorem 2 and Proposition 1
    source-to-finite-SSGM interfaces. Theorem 1's source bridge is closed from
    the visible C1-C3, utility, response-model, and norm-pair hypotheses, so
    Theorem 1 now depends only on the theorem-shaped SSGM convergence boundary.
    Proposition 2's local `L∞` response bridge is now derived from
    decomposable additivity plus an explicit product-coordinate replacement
    property (`DecomposableLinfCoordinateReplacement`). In finite coordinate
    vector models with identity coordinate projections,
    `FiniteCoordinateLinfCoordinateReplacementSource` now derives that
    replacement property from finite `L∞` norm semantics and product-box
    solution-space closure. The median carrier is also derived from an explicit
    coordinate-wise median-set source formula. A fixed-decomposition convergence
    route now consumes those fixed source fields directly, avoiding the stronger
    all-decompositions `Proposition2SourceSemantics` package for that route.
    Theorem 3 has a corrected global-radius projected-trace route: the displayed
    directional field is proved from a finite weighted expectation of normalized
    gradients, the drift contradiction is derived from coordinatewise
    convergence, the finite-dot projection residual geometry is proved, and iid
    weighted-voter finite-dot concentration is proved for the same selected
    voter stream. The public row no longer has an SSGM boundary premise and no
    longer hides an environment-level drift field. The remaining Theorem 3
    source obligation is the explicit deterministic global projected trace
    source in
    `FiniteCoordinateILVFullConcreteSourceModel`, which ties the abstract
    environment trajectory to the selected-voter raw-response/projection process.
  - `EconCSLib.Foundations.Math.FiniteDimensionalNormsDerivative` proves the
    Fréchet derivative of the finite `Lp` power sum for `1 < p`, using
    mathlib's `hasDerivAt_abs_rpow` and finite product projection derivatives.
    GKGMM19 now has wrappers connecting that derivative coefficient through the
    outer `S^(1/p)` chain rule to the Lemma 3 candidate-gradient formula.
  - GKGMM19 also has internal source-shape predicates for Algorithm 1 projection,
    norm-minimizing projection, stopping windows, finite-coordinate projected
    SSGM updates, reported-direction/noise/bias decomposition, and a
    trajectory-level projected SSGM recurrence predicate. It also has a finite
    subgradient predicate and a proof that projected SSGM recurrences preserve
    feasibility after a feasible initial point. The Model B movement formula now
    bridges to projected SSGM, including the sign-correct
    Theorem 2 case where utility-gradient movement by `-∇cost` yields a descent
    step using `∇cost`. Finite-coordinate `Lp` scalar homogeneity is also proved,
    giving the Theorem 2 Model B boundary-distance and within-radius facts.
    The ILV radius facts are packaged as `SSGMStepSizeConditions`, matching the
    step-size side of the external stochastic subgradient convergence theorem.
    Finite `Lp` convexity is derived through mathlib `PiLp`, the convex
    derivative-to-subgradient bridge certifies the Lemma 3 candidate as a finite
    subgradient of each sampled cost, and the bad-event-avoidance wrapper
    packages whole-trajectory Model B responses as projected sample-subgradient
    recurrences with feasible projected iterates.
    Under the structured finite-coordinate C3 product-density carrier, the a.e.
    Lemma 3 inputs also compile: unit Holder-dual candidate norm, sampled `Lp`
    subgradient certification, Model B normalization identity, and
    boundary-distance fact. A paper-radius package combines `ilvRadius`
    step-size conditions, the projected sample-subgradient recurrence, and
    projected-iterate feasibility. Proposition 1's weighted-Euclidean source
    layer now supplies `0 < r0` plus the projected recurrence, and Lean derives
    projected-trajectory feasibility and the SSGM step-size package for the
    proof-facing input record.
    Proof-facing endpoint-specialization corollaries project the broad theorem
    schemas to the concrete Theorem 1 norm/model cases, Theorem 2 Model B
    conclusion, Proposition 1/2 Model A/B conclusions, and Theorem 3
    directional-equilibrium conclusion.
    `FiniteCoordinateILVBoundaryInterfaces` records the strongest current
    replacement for the broad endpoint marker in finite-coordinate
    environments: Theorem 1's closed source bridge plus theorem-shaped SSGM
    boundaries for Theorems 1-2 and Propositions 1-2, source bridges where
    they are still needed. `Theorem2SourceSemantics`,
    `Proposition1SourceSemantics`, and `Proposition2SourceSemantics` expose the
    deterministic non-SSGM source layer, and
    `proof_ilvSSGMConvergenceConsequences_of_sourceSemantics_ssgmBoundaries`
    is the one-call strict handoff theorem from source semantics plus SSGM-only
    boundaries to the four stochastic endpoint consequences.  The direct
    theorem-bundle handoff
    `ilvSSGMConvergenceConsequences_of_sourceSemantics_ssgmConvergence` now
    proves the same consequence bundle from those theorem-specific source
    semantics plus `FiniteCoordinateILVSSGMConvergenceTheorems E`.  The direct
    endpoint handoff theorems
    `theorem2Statement_of_sourceSemantics_ssgmConvergence`,
    `proposition1Statement_of_sourceSemantics_ssgmConvergence`, and
    `proposition2Statement_of_sourceSemantics_ssgmConvergence` make this
    separation explicit before any endpoint consequence bundle is formed.
    `FiniteCoordinateILVConcreteSourceModel` now packages the stronger
    finite-coordinate source interpretation in one record and derives all three
    source-semantics records from that concrete model.  The theorem
    `ilvSSGMConvergenceConsequences_of_concreteSourceModel_ssgmConvergence`
    is the checked one-call handoff from this concrete source model plus the
    theorem-shaped SSGM convergence bundle.
- Exact current mathematical gap:
  - Theorem 1, Theorem 2, Proposition 1, and Proposition 2 depend on the single
    `assumption_ssgm_convergence_theorem` in `Assumptions.lean`, after the
    public rows consume `FiniteCoordinateILVConcreteSourceModel`. The proof
    interface now has a full finite-coordinate closeout theorem,
    `proof_finiteCoordinateILVFullPaperConsequences_of_fullPrimitiveSourceSemantics`,
    which combines those four SSGM-backed rows with Theorem 3 from the concrete
    finite directional field, a separate concrete field-continuity source, and
    split global projected Algorithm 1 update and aggregate feasible-direction
    sources.  The update source exposes norm projection, projected-update, and
    finite-distance fields; the aggregate source exposes the exact feasible
    `G(x*)` direction field consumed by the projection-residual proof. The C1 convexity source and the
    finite-coordinate reading of abstract point convergence are separate
    full-source fields before Lean derives the
    proof-facing deterministic skeleton, almost-sure trace skeleton, and exact
    `theorem3Statement E`.  The granular source record
    `FiniteCoordinateILVFullPrimitiveSourceSemantics` now gives a second full-paper
    closeout route with Theorem 2, Proposition 1, Proposition 2, and Theorem 3
    source semantics kept as separate fields; the proof-facing theorem
    `proof_finiteCoordinateILVFullPaperConsequences_of_fullPrimitiveSourceSemantics`
    consumes only that record and the single SSGM axiom. The remaining
    non-SSGM work is source-model instantiation: prove that the paper's
    abstract C1-C3/Model A/Model B semantics supply these source semantics.
  - The Lean model is still abstract over convergence w.p. 1, stochastic
    subgradient descent / SSGM convergence, the bridge from the paper's C3
    density condition to the structured product-measure bounded-density
    hypothesis, and the final endpoint reductions that invoke the library-level
    convergence theorem. Basic
    finite-coordinate norm semantics, Lemma 3 differentiability, and the
    finite-union/bounded-density transfer step, product atomless nullness, a.e.
    noncollision condition, structured finite-coordinate density carrier,
    projection invariants, finite subgradient certification, a.e. Lemma 3
    SSGM inputs, and Model B projected sample-subgradient recurrence assembly
    are now connected to source-facing formulas and mathlib `PiLp`.
  - A concrete finite Model B ILV trace package now connects the actual
    environment trajectory to the paper-radius SSGM inputs, once source
    response semantics provide projection, selected voter, raw response,
    sampled ideal `E.ideal (voter t)`, and bad-event-avoidance fields.
  - An environment-tied finite-coordinate C3 carrier packages the exact target
    for replacing the abstract `E.idealDistribution_bounded_measurable_density`
    field by concrete product-density ideal-point data.
  - A read-only interface audit confirmed that the current abstract
    `ILVEnvironment` does not contain enough semantics to derive the remaining
    finite source-to-input bridges, the C3 product-density carrier, or the
    Theorem 3 selected-voter/projected-trace alignment from abstract C3 without
    stronger model fields or explicit source-semantics records. Theorem 3's
    finite route now reduces its remaining source-response work to supplying the
    primitive global projected Algorithm 1 trace source and concrete
    field-continuity source, with the C1 convexity source factored out of the
    per-sample trace witness; Lean checks the
    coordinatewise-to-finite-`L2` distance convergence, the neighborhood-escape
    contradiction, the continuity-to-fixed-coordinate-drift lemma, the
    coordinate-escape-to-`L2`-escape reduction, the accumulated
    signed-coordinate-to-coordinate-escape reduction, the one-step
    signed-coordinate telescoping reduction, the expected harmonic
    signed-coordinate drift lower bound from fixed-sign coordinate drift, the
    expected-drift-minus-fluctuation shell, the eventual tail-fluctuation shell,
    exact tail-coordinate telescoping identities for one-step increments, the
    finite-voter expected signed raw Model B increment and finite-sum identities,
    the finite-dot expected raw Model B increment and finite-sum identities,
    the finite-dot eventual Hoeffding shell to paper-radius projected escape,
    the analytic finite-dot positive-drift derivation from coordinate-continuity
    and convergence,
    the raw finite-dot sampled Model B shell to finite-dot fluctuation control,
    the projected finite-dot sampled shell with selected-voter concentration
    plus projection slack,
    the sampled raw Hoeffding shell with visible actual-increment equality, the
    projected raw Hoeffding shell with bounded projection slack, the checked
    zero-slack bridge from exact sampled-raw coordinate semantics to
    projected-raw semantics, the finite-dot zero-slack bridge from exact sampled
    raw scalar increments to the projected finite-dot shell, the finite-dot
    selected-raw residual identity that turns projection slack into a cumulative
    selected-response-to-projected-next residual bound, the residual-bound shell
    that converts this named residual target into the projected finite-dot
    route, the tangent feasible-direction normal-cone lemma that makes
    projection residuals nonpositive when some positive step along `G(x*)`
    remains feasible from projected points,
    the pointwise-to-cumulative zero residual-bound lemma,
    the projected-trace finite-dot bridge that derives the residual-bound shell
    from finite `L2` norm projection, convexity, selected raw responses,
    projected updates, and positive-step feasible `G(x*)` directions,
    the finite `L2` projection identity on feasible raw points and the resulting
    exact selected-response increment equality,
    the proof-interface wrapper around mathlib's Azuma-Hoeffding theorem for
    conditionally sub-Gaussian adapted increments,
    the kernel-level bounded-centered Hoeffding bridge to
    `HasCondSubgaussianMGF`,
    the Azuma/Borel-Cantelli adapter from a summable exponential envelope to
    eventual finite-dot fluctuation control,
    the martingale-convergence adapter from a.e. convergence of centered
    partial sums to finite-dot fluctuation control,
    the `L1`-bounded partial-sum martingale route to that a.e. convergence,
    partial-sum adaptedness from adapted increments,
    conditional-mean-zero partial-sum martingale construction,
    and integrability of finite partial sums from conditional sub-Gaussianity,
    the Borel-Cantelli wrapper from summable bad-event probabilities to
    almost-sure eventual tail control,
    the ENNReal summability conversion from real event-probability bounds,
    the finite-dot `L2` Cauchy-Schwarz and bounded-step increment lemmas,
    and the finite
    norm-projection-to-normal-cone-to-progress algebra
    for projected raw steps,
    including exact Theorem 3 finite-dot projection increment formulas.
    The public endpoint rows are split so that theorem-specific deterministic
    source semantics remain visible. The full closeout route can use either
    `FiniteCoordinateILVFullConcreteSourceModel` or the more granular
    `FiniteCoordinateILVFullPrimitiveSourceSemantics`.
  - Model A local maximization under Definition 1 now supplies direct
    distance-to-ideal improvement inequalities over the queried local
    neighborhood.
- Next bridge lemmas to try:
  - Complete everything except SSGM by instantiating
    `FiniteCoordinateILVFullConcreteSourceModel` from a stronger concrete source
    interpretation. The remaining non-SSGM obligations are:
    construct `Theorem2SourceSemantics` from concrete finite C3/product-density,
    norm-distance, selected-voter raw Model B Algorithm 1 trace source, and
    projection-update data; construct
    `Proposition1ConcreteComponentSourceSemantics` from weighted-Euclidean local
    response, concrete component-distance/ideal data, projected-update
    equations, and social-utility maximizer source formulas, from which Lean
    derives the older `Proposition1SourceSemantics` and minimization objective
    `-societalUtility`; construct
    `Proposition2SourceSemantics` from
    decomposable median-set source formulas and product-box `L∞` replacement data; and derive
    `FiniteTheorem3GlobalProjectedAlgorithm1UpdateSource` from the explicit
    selected-voter Model B route, including norm projection, projected updates
    with global tail radii, finite-distance interpretation, and the pointwise
    trace generator for every sampled voter stream. For feasible `G(x*)`
    directions, Lean now consumes the explicit
    `FiniteTheorem3GlobalProjectedAggregateFeasibilitySource` field. Lean then
    derives the deterministic and AE trace skeletons and combines the AE route with the
    concentration event over the same sampled voter stream.
  - Keep `assumption_ssgm_convergence_theorem` as the only intended library
    boundary. Any other unproved item must appear as a theorem-specific source
    semantics field or be proved from existing concrete records; do not hide it
    inside SSGM.
  - Bridge the paper's C3 bounded-density assumption to the structured
    `HasBoundedDensity (Measure.pi ...)` product-measure hypothesis.
  - Add bounded-density small-ball/slice bounds for the other bad-region
    estimates used by Theorems 1, Proposition 1, and the Model B recurrence.
  - Prove the reusable stochastic approximation theorem that discharges
    `assumption_ssgm_convergence_theorem`; separately, instantiate the
    theorem-specific source semantics from concrete C3/norm/response/objective
    and median records when strengthening the source model beyond the current
    finite-coordinate interface.
- Informal proof sketch / recurrence / construction:
  - Treat Algorithm 2 as an SSGM recurrence on cost, not utility, to avoid sign
    confusion.
  - Split Model A "favorite point in ball" lemmas from stochastic convergence.
  - Use bounded-density lemmas to show bad events have probability `O(r_t)`;
    combine with `sum_t r_t^2 < infinity` for the bias term.

## Deviations And Assumptions

- Source imprecision or proof deviation to report later:
  - The `p > 0` wording in Theorem 2 should be audited against norm/convexity
    requirements.
  - Appendix Lemma 2 appears to duplicate the `(p=1,q=inf)` label where the
    third case should correspond to `(p=inf,q=1)`.
  - The paper uses cost minimization in the appendix after utility maximization
    in the body; Lean should make this conversion explicit.
- Genuine paper assumptions to declare in `Assumptions.lean`:
  - `assumption_conditions_c123`
- Temporary proof-boundary assumptions to declare in `Assumptions.lean`:
  - `assumption_ssgm_convergence_theorem`
- Major human-facing proof boundary:
  - The stochastic subgradient convergence theorem used through the paper's
    Theorem 5 remains an explicit partial-formalization boundary. The intended
    completion route is either an EconCSLib stochastic-approximation theorem
    built from mathlib probability/process APIs, or a future Optlib-backed port
    of the convex/subgradient layer followed by a new stochastic convergence
    proof.
- Temporary certificate fields to discharge:
  - Replace `assumption_ssgm_convergence_theorem` with proofs from a reusable
    stochastic-approximation library.
  - Replace abstract finite-vector/norm semantics with concrete Mathlib/EconCSLib
    coordinate spaces.
  - Derive `Theorem2SourceSemantics`,
    `Proposition1ConcreteComponentSourceSemantics`,
    `Proposition2SourceSemantics`, C3 product-density carriers, and the Theorem
    3 primitive global projected Algorithm 1 trace source plus concrete
    field-continuity source from concrete source response behavior instead of
    treating those source-semantics records as supplied data.
