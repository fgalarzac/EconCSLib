import EconCSLib.Foundations.Probability.QueueingMM1Uniformization
import Mathlib.Probability.Kernel.Invariance
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Countable M/M/1 jump kernels and Mathlib invariance

This module lifts the reflected countable PMF jump kernel to Mathlib's
`Kernel` API.  It transfers PMF stationarity to `Kernel.Invariant` and proves
that every finite-step kernel preserves the geometric stationary marginal.

It still does not construct an infinite stationary trajectory or the
continuous-time Poisson-clock M/M/1 path; those require a separate
Ionescu--Tulcea and time-change construction.
-/

open scoped ENNReal NNReal

namespace EconCSLib.Probability.Queueing

open MeasureTheory ProbabilityTheory

/-- Interpret a countable PMF transition matrix as a Mathlib Markov kernel.
This generic lift is used both for the queue-length chain and for augmented
countable states that carry an event mark. -/
noncomputable def countablePMFKernel
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (K : CountableMarkovKernel α) : Kernel α α :=
  Kernel.ofFunOfCountable fun n => (K n).toMeasure

instance {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (K : CountableMarkovKernel α) : IsMarkovKernel (countablePMFKernel K) where
  isProbabilityMeasure n := by
    change IsProbabilityMeasure ((K n).toMeasure)
    infer_instance

lemma pmf_toMeasure_eq_count_withDensity
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (p : PMF α) :
  p.toMeasure = Measure.count.withDensity p := by
  ext s hs
  rw [PMF.toMeasure_apply_eq_tsum, withDensity_apply _ hs,
    ← lintegral_indicator hs, lintegral_count]

lemma bind_countablePMFKernel_eq_pmf_bind_toMeasure
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (π : PMF α) (K : CountableMarkovKernel α) :
  π.toMeasure.bind (countablePMFKernel K) = (π.bind K).toMeasure := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), countablePMFKernel,
    pmf_toMeasure_eq_count_withDensity π,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_of_countable _)
      (measurable_of_countable _),
    lintegral_count]
  rw [PMF.toMeasure_bind_apply π K s hs]
  rfl

theorem PMFStationary.kernelInvariant
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    {K : CountableMarkovKernel α} {π : PMF α}
    (hstationary : PMFStationary K π) :
    Kernel.Invariant (countablePMFKernel K) π.toMeasure := by
  rw [Kernel.Invariant, bind_countablePMFKernel_eq_pmf_bind_toMeasure, hstationary]

/-- Every finite-step transition kernel preserves the stationary marginal. -/
theorem PMFStationary.kernelInvariant_pow
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    {K : CountableMarkovKernel α} {π : PMF α}
    (hstationary : PMFStationary K π) (n : ℕ) :
    Kernel.Invariant (countablePMFKernel K ^ n) π.toMeasure := by
  induction n with
  | zero =>
      rw [pow_zero, Kernel.Invariant]
      ext s hs
      rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
      change (∫⁻ a, Kernel.id a s ∂π.toMeasure) = π.toMeasure s
      simp_rw [Kernel.id_apply, Measure.dirac_apply' _ hs]
      exact lintegral_indicator_one hs
  | succ n ih =>
      rw [pow_succ]
      exact ih.comp hstationary.kernelInvariant

theorem geoNNPMF_uniformized_kernelInvariant
    (rho : ℝ≥0) (hrho : rho < 1) :
    Kernel.Invariant
      (countablePMFKernel
        (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho)))
      (geoNNPMF rho hrho).toMeasure :=
  (geoNNPMF_uniformized_stationary rho hrho).kernelInvariant

end EconCSLib.Probability.Queueing
