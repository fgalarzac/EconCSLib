import GKGMM19IterativeLocalVoting.MainTheorems
import Mathlib.Probability.Martingale.Convergence

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators MeasureTheory

/-!
# Paper Assumptions: Iterative Local Voting for Collective Decision-making in Continuous Spaces

This file is the only paper-local place for assumptions that are not derived in
Lean. Keep it small. Each declaration must be explicitly stated by the paper,
listed in `status.json` `review_surface.assumption_names`, and judged in
`assumption_match_llm.json` as a true source/model assumption rather than a
proof convenience.

Use `-- audit-premise: <exact Lean binder>` comments to route hidden theorem
premises to an approved assumption declaration when the audit reports an exact
binder string.

## Paper Assumptions

- `assumption_conditions_c123`: source assumptions C1, C2, and C3.
- `assumption_ssgm_convergence_theorem`: the concrete proposition corresponding
  to the external stochastic subgradient convergence theorem. It has no global
  proof; reviewed paper endpoints remain explicit proof obligations.
  Theorem 3 is derived separately from the concrete finite directional field
  and the deterministic global projected trace source carried by
  `FiniteCoordinateILVFullConcreteSourceModel`, rather than being hidden in the
  SSGM boundary or in an abstract environment drift field.
- `assumption_expected_subgradient_theorem`: a proved finite-coordinate,
  general-probability-space form of Appendix Theorem 4 with every
  integrability obligation explicit.
-/

namespace GKGMM19IterativeLocalVoting

/--
Source assumptions C1, C2, and C3 from Section 3:
nonempty bounded closed convex solution space, unique ideal points, and a
bounded measurable density for independently drawn ideal points.
-/
-- audit-premise: hC : assumption_conditions_c123 E
abbrev assumption_conditions_c123 {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) : Prop :=
  E.solutionSpace_nonempty_bounded_closed_convex ∧
    E.uniqueIdealSolutions ∧
      E.idealDistribution_bounded_measurable_density

/-- Finite-coordinate subgradient inequality restricted to a feasible set. -/
def FiniteSubgradientWithinAt
    {Coord : Type*} [Fintype Coord]
    (cost : (Coord → ℝ) → ℝ) (solutionSpace : Set (Coord → ℝ))
    (x g : Coord → ℝ) : Prop :=
  ∀ y, y ∈ solutionSpace →
    cost x +
      EconCSLib.FiniteDimensionalNorms.coordinateLinearFunctional g
        (fun i => y i - x i) ≤ cost y

/-- Appendix Theorem 4's expected objective and expected selected gradient. -/
def ExpectedSubgradientTheoremStatement
    {Theta Coord : Type*} [MeasurableSpace Theta] [Fintype Coord]
    (mu : Measure Theta)
    (solutionSpace : Set (Coord → ℝ))
    (sampleCost : Theta → (Coord → ℝ) → ℝ)
    (x : Coord → ℝ) (sampleGradient : Theta → Coord → ℝ) : Prop :=
  FiniteSubgradientWithinAt
    (fun y => ∫ theta, sampleCost theta y ∂mu)
    solutionSpace
    x
    (fun i => ∫ theta, sampleGradient theta i ∂mu)

/--
Finite-coordinate, measure-theoretic form of Appendix Theorem 4.  The two
integrability hypotheses are the formal content of the paper's requirement
that the displayed expectations be well-defined.  The proof integrates the
sample subgradient inequality and commutes a finite coordinate sum with the
integral.
-/
theorem assumption_expected_subgradient_theorem
    {Theta Coord : Type*} [MeasurableSpace Theta] [Fintype Coord]
    (mu : Measure Theta) [IsProbabilityMeasure mu]
    (solutionSpace : Set (Coord → ℝ))
    (sampleCost : Theta → (Coord → ℝ) → ℝ)
    (x : Coord → ℝ) (sampleGradient : Theta → Coord → ℝ)
    (_hX_nonempty : solutionSpace.Nonempty)
    (_hX_bounded : Bornology.IsBounded solutionSpace)
    (_hX_closed : IsClosed solutionSpace)
    (_hX_convex : Convex ℝ solutionSpace)
    (_hx : x ∈ solutionSpace)
    (hcost_integrable :
      ∀ y, y ∈ solutionSpace →
        Integrable (fun theta => sampleCost theta y) mu)
    (hgradient_integrable :
      ∀ i, Integrable (fun theta => sampleGradient theta i) mu)
    (_hsample_convex :
      ∀ theta, ConvexOn ℝ solutionSpace (sampleCost theta))
    (_hexpected_continuous :
      ContinuousAt (fun y => ∫ theta, sampleCost theta y ∂mu) x)
    (hsample :
      ∀ theta,
        FiniteSubgradientWithinAt
          (sampleCost theta) solutionSpace x (sampleGradient theta)) :
    ExpectedSubgradientTheoremStatement
      mu solutionSpace sampleCost x sampleGradient := by
  intro y hy
  let d : Coord → ℝ := fun i => y i - x i
  have hlinear_integrable :
      Integrable
        (fun theta =>
          EconCSLib.FiniteDimensionalNorms.coordinateLinearFunctional
            (sampleGradient theta) d) mu := by
    simp_rw [coordinateLinearFunctional_apply]
    exact MeasureTheory.integrable_finset_sum Finset.univ (by
      intro i _hi
      exact (hgradient_integrable i).mul_const (d i))
  have hlinear_integral :
      EconCSLib.FiniteDimensionalNorms.coordinateLinearFunctional
          (fun i => ∫ theta, sampleGradient theta i ∂mu) d =
        ∫ theta,
          EconCSLib.FiniteDimensionalNorms.coordinateLinearFunctional
            (sampleGradient theta) d ∂mu := by
    simp_rw [coordinateLinearFunctional_apply]
    rw [MeasureTheory.integral_finset_sum]
    · simp_rw [MeasureTheory.integral_mul_const]
    · intro i _hi
      exact (hgradient_integrable i).mul_const (d i)
  rw [hlinear_integral]
  rw [← MeasureTheory.integral_add
    (hcost_integrable x _hx) hlinear_integrable]
  apply MeasureTheory.integral_mono_ae
  · exact (hcost_integrable x _hx).add hlinear_integrable
  · exact hcost_integrable y hy
  · exact Filter.Eventually.of_forall (fun theta => hsample theta y hy)

/--
Concrete source-shaped statement of Appendix Theorem 5. It exposes the
probability space, filtration, bounded closed convex feasible set, convex
objective with a unique minimizer, projected update, step sizes, subgradients,
conditional mean-zero noise, conditional bounded second moments, bounded bias,
and almost-sure summability before concluding almost-sure convergence.
-/
def AppendixTheorem5Statement
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega}
    [Fintype Coord] [Nonempty Coord]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (solutionSpace : Set (Coord → ℝ))
    (objective : (Coord → ℝ) → ℝ)
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory meanSubgradient noise : ℕ → Omega → Coord → ℝ)
    (bias : ℕ → Coord → ℝ)
    (radius : ℕ → ℝ) (xstar : Coord → ℝ) : Prop :=
  solutionSpace.Nonempty ∧
    Bornology.IsBounded solutionSpace ∧
    IsClosed solutionSpace ∧
    Convex ℝ solutionSpace ∧
    ConvexOn ℝ solutionSpace objective ∧
    xstar ∈ solutionSpace ∧
    IsMinOn objective solutionSpace xstar ∧
    (∀ y, y ∈ solutionSpace → objective y = objective xstar → y = xstar) ∧
    SSGMStepSizeConditions radius ∧
    (∀ y,
      project y ∈ solutionSpace ∧
        IsMinOn
          (fun x => finiteCoordinateDistance SourceNorm.l2 x y)
          solutionSpace (project y)) ∧
    (∀ t, ∀ᵐ omega ∂mu,
      trajectory (t + 1) omega =
        project (fun i =>
          trajectory t omega i -
            radius (t + 1) *
              (meanSubgradient t omega i + noise t omega i + bias t i))) ∧
    (∀ i, StronglyAdapted filtration (fun t omega => trajectory t omega i)) ∧
    (∀ i, StronglyAdapted filtration
      (fun t omega => meanSubgradient t omega i)) ∧
    (∀ t, ∀ᵐ omega ∂mu,
      trajectory t omega ∈ solutionSpace ∧
        FiniteSubgradientWithinAt objective solutionSpace (trajectory t omega)
          (meanSubgradient t omega)) ∧
    (∃ C1 : ℝ, 0 ≤ C1 ∧
      ∀ x, x ∈ solutionSpace → ∀ g,
        FiniteSubgradientWithinAt objective solutionSpace x g →
          finiteCoordinateNorm SourceNorm.l2 g ≤ C1) ∧
    (∀ t i, Integrable (fun omega => noise t omega i) mu) ∧
    (∀ t i, mu[fun omega => noise t omega i | filtration t] =ᵐ[mu] 0) ∧
    (∀ t, Integrable (fun omega =>
      finiteCoordinateNorm SourceNorm.l2 (noise t omega) ^ 2) mu) ∧
    (∃ C2 : ℝ, 0 ≤ C2 ∧
      ∀ t,
        mu[fun omega =>
          finiteCoordinateNorm SourceNorm.l2 (noise t omega) ^ 2 | filtration t]
            ≤ᵐ[mu] fun _ => C2) ∧
    (∃ C3 : ℝ, 0 ≤ C3 ∧
      ∀ t, finiteCoordinateNorm SourceNorm.l2 (bias t) ≤ C3) ∧
    Summable (fun t =>
      radius (t + 1) * finiteCoordinateNorm SourceNorm.l2 (bias t)) →
    ∀ᵐ omega ∂mu,
      Tendsto (fun t => trajectory t omega) atTop (nhds xstar)

/-- Named paper boundary proposition; no proof is postulated here. -/
def assumption_ssgm_convergence_theorem := @AppendixTheorem5Statement

/--
Apply an explicit SSGM convergence bundle to a concrete finite-coordinate
source model to obtain the named four-endpoint consequence bundle.
-/
theorem ssgm_convergence_theorem_consequences
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVConcreteSourceModel E)
    (S : FiniteCoordinateILVSSGMConvergenceTheorems E) :
    ILVSSGMConvergenceConsequences E :=
  ilvSSGMConvergenceConsequences_of_concreteSourceModel_ssgmConvergence
    M S

end GKGMM19IterativeLocalVoting
