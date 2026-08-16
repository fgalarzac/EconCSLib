import EconCSLib.Foundations.Probability.QueueingMM1TrajectoryTransition
import Mathlib.Probability.HasLaw

/-!
# Independent random-index laws of stationary trajectories

The index is sampled independently either directly from a probability measure
on `ℕ` or as a measurable natural-valued variable on a separate product-space
clock factor. Since every fixed coordinate has stationary marginal, evaluating
at either independent index retains the same marginal.  For initial/current
pairs, the product construction gives the exact mixture of embedded `n`-step
pair laws. This does not cover a trajectory-dependent stopping index, an
endogenous time change, or a Palm tag.
-/

namespace EconCSLib.Probability.Queueing

open MeasureTheory ProbabilityTheory

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- Evaluation of a trajectory at an independently sampled discrete index. -/
def stationaryTrajectoryAtIndependentIndex : (ℕ → α) × ℕ → α :=
  fun z => z.1 z.2

theorem measurable_stationaryTrajectoryAtIndependentIndex :
    Measurable (stationaryTrajectoryAtIndependentIndex (α := α)) := by
  exact measurable_from_prod_countable_left (fun n => measurable_pi_apply n)

/--
Any process whose deterministic-time marginals are all `π` retains marginal
law `π` when evaluated at an independently sampled natural-number index.
Independence is represented by the product measure.
-/
theorem trajectory_eval_independentIndex_hasLaw_of_marginals
    {μ : Measure (ℕ → α)} [IsProbabilityMeasure μ] {π : Measure α}
    (hmarginal : ∀ n : ℕ, μ.map (fun x => x n) = π)
    (ν : Measure ℕ) [IsProbabilityMeasure ν] :
    ProbabilityTheory.HasLaw (stationaryTrajectoryAtIndependentIndex (α := α)) π
      (μ.prod ν) := by
  have heval : Measurable (stationaryTrajectoryAtIndependentIndex (α := α)) :=
    measurable_stationaryTrajectoryAtIndependentIndex
  refine ⟨heval.aemeasurable, ?_⟩
  ext s hs
  rw [Measure.map_apply heval hs, Measure.prod_apply_symm (heval hs)]
  have hcoordinate : ∀ n : ℕ,
      μ
        ((fun x : ℕ → α => (x, n)) ⁻¹'
          (stationaryTrajectoryAtIndependentIndex (α := α) ⁻¹' s)) = π s := by
    intro n
    have hmap := hmarginal n
    have hmap_apply := congrArg (fun η : Measure α => η s) hmap
    change (Measure.map (fun x : ℕ → α => x n) μ) s = π s at hmap_apply
    rw [Measure.map_apply (measurable_pi_apply n) hs] at hmap_apply
    simpa [stationaryTrajectoryAtIndependentIndex] using hmap_apply
  calc
    ∫⁻ n, μ
        ((fun x : ℕ → α => (x, n)) ⁻¹'
          (stationaryTrajectoryAtIndependentIndex (α := α) ⁻¹' s)) ∂ν =
        ∫⁻ _ : ℕ, π s ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [] with n
      exact hcoordinate n
    _ = π s * ν Set.univ := lintegral_const _
    _ = π s := by simp

/--
If `K` preserves `π`, then a stationary trajectory evaluated at an
independently sampled `ℕ`-valued index has law `π`.  Independence is expressed
by the product measure; `ν` may be any probability law on natural numbers.
-/
theorem stationaryTrajMeasure_eval_independentIndex_hasLaw
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    (hstationary : Kernel.Invariant K π) (ν : Measure ℕ) [IsProbabilityMeasure ν] :
    ProbabilityTheory.HasLaw (stationaryTrajectoryAtIndependentIndex (α := α)) π
      ((stationaryTrajMeasure π K).prod ν) := by
  letI : IsProbabilityMeasure (stationaryTrajMeasure π K) := by
    unfold stationaryTrajMeasure
    infer_instance
  exact trajectory_eval_independentIndex_hasLaw_of_marginals
    (fun n => stationaryTrajMeasure_marginal hstationary n) ν

/-- Evaluation of a trajectory at a measurable natural-valued index carried by
an independent external factor. -/
theorem measurable_trajectoryAtIndependentRandomIndex
    {Ω : Type*} [MeasurableSpace Ω]
    (C : Ω → ℕ) (hC : Measurable C) :
    Measurable (fun z : (ℕ → α) × Ω => z.1 (C z.2)) := by
  exact measurable_stationaryTrajectoryAtIndependentIndex.comp
    (measurable_fst.prodMk (hC.comp measurable_snd))

/--
An arbitrary measurable external natural-number index preserves the marginal
of a process with identical deterministic-time marginals when sampled under
the product law. The result is agnostic to the distribution of `C`; product
measure is its entire independence assumption.
-/
theorem trajectory_eval_independentRandomIndex_hasLaw_of_marginals
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (ℕ → α)} [IsProbabilityMeasure μ] {π : Measure α}
    (hmarginal : ∀ n : ℕ, μ.map (fun x => x n) = π)
    {P : Measure Ω} [IsProbabilityMeasure P]
    (C : Ω → ℕ) (hC : Measurable C) :
    ProbabilityTheory.HasLaw (fun z : (ℕ → α) × Ω => z.1 (C z.2)) π
      (μ.prod P) := by
  have heval : Measurable (fun z : (ℕ → α) × Ω => z.1 (C z.2)) :=
    measurable_trajectoryAtIndependentRandomIndex C hC
  refine ⟨heval.aemeasurable, ?_⟩
  ext s hs
  rw [Measure.map_apply heval hs, Measure.prod_apply_symm (heval hs)]
  have hcoordinate : ∀ ω : Ω,
      μ ((fun x : ℕ → α => (x, ω)) ⁻¹'
        ((fun z : (ℕ → α) × Ω => z.1 (C z.2)) ⁻¹' s)) = π s := by
    intro ω
    have hmap := hmarginal (C ω)
    have hmap_apply := congrArg (fun η : Measure α => η s) hmap
    change (Measure.map (fun x : ℕ → α => x (C ω)) μ) s = π s at hmap_apply
    rw [Measure.map_apply (measurable_pi_apply (C ω)) hs] at hmap_apply
    simpa using hmap_apply
  calc
    ∫⁻ ω, μ ((fun x : ℕ → α => (x, ω)) ⁻¹'
        ((fun z : (ℕ → α) × Ω => z.1 (C z.2)) ⁻¹' s)) ∂P =
        ∫⁻ _ : Ω, π s ∂P := by
      apply lintegral_congr_ae
      filter_upwards [] with ω
      exact hcoordinate ω
    _ = π s * P Set.univ := lintegral_const _
    _ = π s := by simp

/--
Stationary trajectories inherit their invariant marginal at any independently
sampled measurable external natural-number index. For example, `C` may be the
count at a fixed time of a separately supplied forward Poisson clock.
-/
theorem stationaryTrajMeasure_eval_independentRandomIndex_hasLaw
    {Ω : Type*} [MeasurableSpace Ω]
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    (hstationary : Kernel.Invariant K π)
    {P : Measure Ω} [IsProbabilityMeasure P]
    (C : Ω → ℕ) (hC : Measurable C) :
    ProbabilityTheory.HasLaw (fun z : (ℕ → α) × Ω => z.1 (C z.2)) π
      ((stationaryTrajMeasure π K).prod P) := by
  letI : IsProbabilityMeasure (stationaryTrajMeasure π K) := by
    unfold stationaryTrajMeasure
    infer_instance
  exact trajectory_eval_independentRandomIndex_hasLaw_of_marginals
    (fun n => stationaryTrajMeasure_marginal hstationary n) C hC

/--
An independently indexed trajectory coordinate is jointly independent of the
external index when all of its deterministic coordinates have law `π`.  This
is a product-space fixed-index fact only: it does not construct a
clock-driven CTMC, marked thinning, a Palm law, or PASTA.
-/
theorem trajectory_eval_independentRandomIndex_joint_hasLaw_of_marginals
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (ℕ → α)} [IsProbabilityMeasure μ] {π : Measure α}
    (hmarginal : ∀ n : ℕ, μ.map (fun x => x n) = π)
    {P : Measure Ω} [IsProbabilityMeasure P]
    (C : Ω → ℕ) (hC : Measurable C) :
    HasLaw (fun z : (ℕ → α) × Ω => (z.1 (C z.2), C z.2))
      (π.prod (P.map C)) (μ.prod P) := by
  letI : IsProbabilityMeasure π := by
    constructor
    rw [← hmarginal 0, Measure.map_apply (measurable_pi_apply 0)
      MeasurableSet.univ]
    simp
  letI : IsFiniteMeasure μ := ⟨by simp⟩
  letI : IsFiniteMeasure π := ⟨by simp⟩
  letI : IsFiniteMeasure P := ⟨by simp⟩
  have heval : Measurable
      (fun z : (ℕ → α) × Ω => (z.1 (C z.2), C z.2)) :=
    (measurable_trajectoryAtIndependentRandomIndex C hC).prodMk
      (hC.comp measurable_snd)
  refine ⟨heval.aemeasurable, ?_⟩
  ext s hs
  rw [Measure.map_apply heval hs, Measure.prod_apply_symm (heval hs)]
  have hcoordinate : ∀ ω : Ω,
      μ ((fun x : ℕ → α => (x, ω)) ⁻¹'
        ((fun z : (ℕ → α) × Ω => (z.1 (C z.2), C z.2)) ⁻¹' s)) =
        π ((fun a : α => (a, C ω)) ⁻¹' s) := by
    intro ω
    have hfiber : MeasurableSet ((fun a : α => (a, C ω)) ⁻¹' s) :=
      hs.preimage (measurable_id.prodMk measurable_const)
    have hmap_apply :
        (Measure.map (fun x : ℕ → α => x (C ω)) μ)
            ((fun a : α => (a, C ω)) ⁻¹' s) =
          π ((fun a : α => (a, C ω)) ⁻¹' s) :=
      congrArg
        (fun η : Measure α => η ((fun a : α => (a, C ω)) ⁻¹' s))
        (hmarginal (C ω))
    rw [Measure.map_apply (measurable_pi_apply (C ω)) hfiber] at hmap_apply
    simpa using hmap_apply
  calc
    ∫⁻ ω, μ ((fun x : ℕ → α => (x, ω)) ⁻¹'
        ((fun z : (ℕ → α) × Ω => (z.1 (C z.2), C z.2)) ⁻¹' s)) ∂P =
        ∫⁻ ω, π ((fun a : α => (a, C ω)) ⁻¹' s) ∂P := by
          apply lintegral_congr_ae
          filter_upwards [] with ω
          exact hcoordinate ω
    _ = ∫⁻ n, π ((fun a : α => (a, n)) ⁻¹' s) ∂(P.map C) := by
          rw [MeasureTheory.lintegral_map (measurable_of_countable _) hC]
    _ = (π.prod (P.map C)) s := by
          rw [Measure.prod_apply_symm hs]

/--
For a stationary embedded chain, the state at an independent external index
and that index have the product joint law.  This remains a fixed-index
product-space statement, not a Poisson thinning, Palm, or PASTA result.
-/
theorem stationaryTrajMeasure_eval_independentRandomIndex_joint_hasLaw
    {Ω : Type*} [MeasurableSpace Ω]
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    (hstationary : Kernel.Invariant K π)
    {P : Measure Ω} [IsProbabilityMeasure P]
    (C : Ω → ℕ) (hC : Measurable C) :
    HasLaw (fun z : (ℕ → α) × Ω => (z.1 (C z.2), C z.2))
      (π.prod (P.map C)) ((stationaryTrajMeasure π K).prod P) := by
  letI : IsProbabilityMeasure (stationaryTrajMeasure π K) := by
    unfold stationaryTrajMeasure
    infer_instance
  exact trajectory_eval_independentRandomIndex_joint_hasLaw_of_marginals
    (fun n => stationaryTrajMeasure_marginal hstationary n) C hC

/-- An external measurable natural-number index on the product probability
space mixes the deterministic initial/current pair laws according to its own
pushforward law.  The product measure is the full independence assumption.
This is not a trajectory-dependent stopping-index theorem and does not
construct a Palm-tagged arrival law. -/
theorem stationaryTrajMeasure_zero_externalIndex_pair_mixture
    {Ω : Type*} [MeasurableSpace Ω]
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (C : Ω → ℕ) (hC : Measurable C)
    (s : Set (α × α)) (hs : MeasurableSet s) :
    ((stationaryTrajMeasure π K).prod P).map
        (fun z : (ℕ → α) × Ω => (z.1 0, z.1 (C z.2))) s =
      ∫⁻ n, (π ⊗ₘ (K ^ n)) s ∂(P.map C) := by
  letI : IsProbabilityMeasure (stationaryTrajMeasure π K) := by
    unfold stationaryTrajMeasure
    infer_instance
  have heval : Measurable
      (fun z : (ℕ → α) × Ω => (z.1 0, z.1 (C z.2))) :=
    ((measurable_pi_apply 0).comp measurable_fst).prodMk
      (measurable_trajectoryAtIndependentRandomIndex C hC)
  rw [Measure.map_apply heval hs, Measure.prod_apply_symm (heval hs)]
  have hcoordinate : ∀ ω : Ω,
      (stationaryTrajMeasure π K)
          ((fun x : ℕ → α => (x, ω)) ⁻¹'
            ((fun z : (ℕ → α) × Ω => (z.1 0, z.1 (C z.2))) ⁻¹' s)) =
        (π ⊗ₘ (K ^ (C ω))) s := by
    intro ω
    have hmap := stationaryTrajMeasure_zero_n_pair (π := π) (K := K) (C ω)
    have hmap_apply := congrArg (fun η : Measure (α × α) => η s) hmap
    change (Measure.map (fun x : ℕ → α => (x 0, x (C ω)))
      (stationaryTrajMeasure π K)) s = (π ⊗ₘ (K ^ (C ω))) s at hmap_apply
    rw [Measure.map_apply
      ((measurable_pi_apply 0).prodMk (measurable_pi_apply (C ω))) hs] at hmap_apply
    simpa using hmap_apply
  calc
    ∫⁻ ω, (stationaryTrajMeasure π K)
        ((fun x : ℕ → α => (x, ω)) ⁻¹'
          ((fun z : (ℕ → α) × Ω => (z.1 0, z.1 (C z.2))) ⁻¹' s)) ∂P =
        ∫⁻ ω, (π ⊗ₘ (K ^ (C ω))) s ∂P := by
      apply lintegral_congr_ae
      filter_upwards [] with ω
      exact hcoordinate ω
    _ = ∫⁻ n, (π ⊗ₘ (K ^ n)) s ∂(P.map C) := by
      rw [MeasureTheory.lintegral_map (measurable_of_countable _) hC]

end

end EconCSLib.Probability.Queueing
