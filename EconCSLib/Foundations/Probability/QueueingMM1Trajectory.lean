import EconCSLib.Foundations.Probability.QueueingMM1Kernel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Stationary discrete-time trajectories for invariant Markov kernels

This module constructs the Ionescu--Tulcea trajectory of a homogeneous Markov
kernel started from an invariant probability measure.  It proves that every
coordinate has the original invariant marginal, then instantiates the result
for the uniformized stable M/M/1 jump kernel.

It is a discrete-time stationary embedded-chain construction.  It does not
yet couple an independent Poisson clock, identify the continuous-time M/M/1
semigroup, or construct the stationary Palm arrival law.
-/

open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory
open Preorder

namespace EconCSLib.Probability.Queueing

variable {α : Type*} [MeasurableSpace α]

noncomputable def homogeneousTrajKernel (K : Kernel α α) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → α) α :=
  K ∘ₖ Kernel.deterministic (fun x => x ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
    (measurable_pi_apply _)

instance homogeneousTrajKernel.isMarkovKernel (K : Kernel α α) [IsMarkovKernel K]
    (n : ℕ) : IsMarkovKernel (homogeneousTrajKernel K n) := by
  unfold homogeneousTrajKernel
  infer_instance

noncomputable def stationaryTrajMeasure (π : Measure α) (K : Kernel α α)
    [IsMarkovKernel K] : Measure (ℕ → α) :=
  Kernel.trajMeasure (X := fun _ : ℕ => α) π (homogeneousTrajKernel K)

theorem stationaryTrajMeasure_succ_marginal
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    (a : ℕ) :
    (stationaryTrajMeasure π K).map (fun x => x (a + 1)) =
      K ∘ₘ (stationaryTrajMeasure π K).map (fun x => x a) := by
  have h := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ : ℕ => α) (μ₀ := π) (κ := homogeneousTrajKernel K) (a := a)
  have hsnd := congrArg Measure.snd h
  rw [Measure.snd_compProd] at hsnd
  change (K ∘ₖ Kernel.deterministic
      (fun x : (i : Finset.Iic a) → α => x ⟨a, Finset.mem_Iic.mpr le_rfl⟩)
      (measurable_pi_apply _)) ∘ₘ
      (stationaryTrajMeasure π K).map (Preorder.frestrictLe a) = _ at hsnd
  change (K ∘ₖ Kernel.deterministic
      (fun x : (i : Finset.Iic a) → α => x ⟨a, Finset.mem_Iic.mpr le_rfl⟩)
      (measurable_pi_apply _)) ∘ₘ
      (stationaryTrajMeasure π K).map (Preorder.frestrictLe a) =
      Measure.map Prod.snd
        (Measure.map (fun x : ℕ → α => (Preorder.frestrictLe a x, x (a + 1)))
          (stationaryTrajMeasure π K)) at hsnd
  rw [← Measure.comp_assoc, Measure.deterministic_comp_eq_map] at hsnd
  have hlast : Measurable (fun x : (i : Finset.Iic a) → α =>
      x ⟨a, Finset.mem_Iic.mpr le_rfl⟩) := measurable_pi_apply _
  rw [Measure.map_map hlast (measurable_frestrictLe a)] at hsnd
  have hpair : Measurable (fun x : ℕ → α => (Preorder.frestrictLe a x, x (a + 1))) :=
    (measurable_frestrictLe a).prodMk (measurable_pi_apply _)
  rw [Measure.map_map measurable_snd hpair] at hsnd
  simpa only [Function.comp_apply, Preorder.frestrictLe_apply] using hsnd.symm

theorem stationaryTrajMeasure_zero_marginal
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K] :
    (stationaryTrajMeasure π K).map (fun x => x 0) = π := by
  unfold stationaryTrajMeasure Kernel.trajMeasure
  rw [Measure.map_comp _ _ (measurable_pi_apply _)]
  have hlast0 : Measurable (fun x : (i : Finset.Iic 0) → α =>
      x ⟨0, Finset.mem_Iic.mpr le_rfl⟩) := measurable_pi_apply _
  have hcoord :
      (Kernel.traj (homogeneousTrajKernel K) 0).map (fun x : ℕ → α => x 0) =
        Kernel.deterministic (fun x : (i : Finset.Iic 0) → α =>
          x ⟨0, Finset.mem_Iic.mpr le_rfl⟩) hlast0 := by
    have hfun : (fun x : ℕ → α => x 0) =
        (fun y : (i : Finset.Iic 0) → α =>
          y ⟨0, Finset.mem_Iic.mpr le_rfl⟩) ∘ Preorder.frestrictLe 0 := by
      funext x
      rfl
    rw [hfun, Kernel.map_comp_right _ (measurable_frestrictLe 0) hlast0,
      Kernel.traj_map_frestrictLe_of_le (X := fun _ : ℕ => α)
        (κ := homogeneousTrajKernel K) (a := 0) (b := 0) le_rfl]
    rw [Kernel.deterministic_map
      (f := Preorder.frestrictLe₂ (π := fun _ : ℕ => α) le_rfl)
      (g := fun y : (i : Finset.Iic 0) → α =>
        y ⟨0, Finset.mem_Iic.mpr le_rfl⟩)
      (measurable_frestrictLe₂ le_rfl) hlast0]
    rfl
  rw [hcoord, Measure.deterministic_comp_eq_map,
    Measure.map_map (measurable_pi_apply _)
      (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => α)).symm.measurable]
  convert (Measure.map_id (μ := π)) using 1

theorem stationaryTrajMeasure_marginal
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    (hstationary : Kernel.Invariant K π) (n : ℕ) :
    (stationaryTrajMeasure π K).map (fun x => x n) = π := by
  induction n with
  | zero => exact stationaryTrajMeasure_zero_marginal
  | succ n ih =>
      rw [stationaryTrajMeasure_succ_marginal, ih, hstationary.def]

theorem geoNNPMF_uniformized_stationaryTraj_marginal
    (rho : ℝ≥0) (hrho : rho < 1) (n : ℕ) :
    (stationaryTrajMeasure
      (geoNNPMF rho hrho).toMeasure
      (countablePMFKernel
        (reflectedBirthDeathKernel
          (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho)))).map
        (fun x => x n) =
      (geoNNPMF rho hrho).toMeasure := by
  exact stationaryTrajMeasure_marginal
    (geoNNPMF_uniformized_kernelInvariant rho hrho) n

/-- The rate-specialized uniformized M/M/1 embedded trajectory retains its
geometric traffic-intensity marginal at every discrete jump index. -/
theorem mm1_uniformized_stationaryTraj_marginal
    (arrivalRate serviceRate : ℝ≥0) (hstable : arrivalRate < serviceRate)
    (n : ℕ) :
    (stationaryTrajMeasure
      (geoNNPMF (mm1TrafficIntensityNN arrivalRate serviceRate)
        (mm1TrafficIntensityNN_lt_one hstable)).toMeasure
      (countablePMFKernel
        (reflectedBirthDeathKernel
          (arrivalRate / (arrivalRate + serviceRate))
          (rate_fraction_le_one arrivalRate serviceRate)))).map
        (fun x => x n) =
      (geoNNPMF (mm1TrafficIntensityNN arrivalRate serviceRate)
        (mm1TrafficIntensityNN_lt_one hstable)).toMeasure := by
  exact stationaryTrajMeasure_marginal
    (mm1_uniformized_geometric_stationary arrivalRate serviceRate hstable).kernelInvariant n

end EconCSLib.Probability.Queueing
