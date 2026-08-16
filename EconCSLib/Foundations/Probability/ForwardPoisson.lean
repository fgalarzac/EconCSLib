import EconCSLib.Foundations.Probability.PoissonProcess
import EconCSLib.Foundations.Probability.PoissonMoments
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.StrongLaw

namespace EconCSLib
namespace Probability
namespace PoissonProcess

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

/-!
# Forward post-tag homogeneous Poisson counting processes

This is the future-facing process interface needed after a tagged Palm
arrival: time is indexed by `ℝ≥0`, so no values before the tag are present.
The zero count is merely the baseline for *future* increments.  In particular,
this interface does not assert two-sided stationarity, construct a Palm
measure, or establish independence from a tagged queue state.
-/

/--
A positive-rate homogeneous Poisson counting process on a forward time axis.

The probability-law field deliberately makes this suitable for a
stationary/Palm law once the caller separately constructs that law.  It says
nothing about how that Palm law was obtained.  `HasIndepIncrements` is the
mathlib process predicate, specialized here to `ℝ≥0` time.
-/
structure ForwardHomogeneousPoissonCountingProcessByLaw
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) where
  /-- The forward process is carried by a probability law. -/
  isProbability : IsProbabilityMeasure P
  rate : ℝ
  rate_pos : 0 < rate
  count : ℝ≥0 → Ω → ℕ
  count_measurable : ∀ t, Measurable (count t)
  count_zero_ae : ∀ᵐ ω ∂P, count 0 ω = 0
  count_mono_ae : ∀ᵐ ω ∂P, Monotone fun t => count t ω
  hasIndepIncrements : ProbabilityTheory.HasIndepIncrements count P
  increment_hasLaw :
    ∀ {s t : ℝ≥0} (hst : s ≤ t),
      ProbabilityTheory.HasLaw
        (fun ω : Ω => count t ω - count s ω)
        (ProbabilityTheory.poissonMeasure
          (rateExposureParam rate ((t : ℝ) - (s : ℝ))
            (mul_nonneg (le_of_lt rate_pos)
              (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst))))) P

namespace ForwardHomogeneousPoissonCountingProcessByLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The nonnegative forward Poisson rate is nonnegative as a real number. -/
theorem rate_nonneg
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P) :
    0 ≤ H.rate :=
  le_of_lt H.rate_pos

/-- Each forward count coordinate is measurable. -/
theorem measurable_count
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (t : ℝ≥0) :
    Measurable (H.count t) :=
  H.count_measurable t

/-- On the discrete count codomain, coordinate measurability gives strong measurability. -/
theorem stronglyMeasurable_count
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (t : ℝ≥0) :
    StronglyMeasurable (H.count t) :=
  (H.measurable_count t).stronglyMeasurable

/--
The count accumulated in the forward interval `[s,t]`.  It is only defined
for forward times, so it cannot accidentally be used to reason about the
pre-tag past.
-/
def intervalCount
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (s t : ℝ≥0) (ω : Ω) : ℕ :=
  H.count t ω - H.count s ω

/-- Forward interval counts are measurable random variables. -/
theorem measurable_intervalCount
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (s t : ℝ≥0) :
    Measurable (H.intervalCount s t) := by
  exact (H.measurable_count t).sub (H.measurable_count s)

/-- Forward count paths are almost surely monotone. -/
theorem count_mono
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P) :
    ∀ᵐ ω ∂P, Monotone fun t => H.count t ω :=
  H.count_mono_ae

/-- Ordered forward-time count coordinates are almost surely ordered. -/
theorem count_le_ae
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    ∀ᵐ ω ∂P, H.count s ω ≤ H.count t ω := by
  filter_upwards [H.count_mono_ae] with ω hmono
  exact hmono hst

/-- The forward interval count has its specified Mathlib Poisson law. -/
theorem intervalCount_hasLaw
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    ProbabilityTheory.HasLaw
      (fun ω : Ω => H.intervalCount s t ω)
      (ProbabilityTheory.poissonMeasure
        (rateExposureParam H.rate ((t : ℝ) - (s : ℝ))
          (mul_nonneg H.rate_nonneg
            (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst))))) P := by
  simpa [intervalCount] using H.increment_hasLaw hst

/-- Real-valued PMF formula for a forward interval count. -/
theorem intervalCount_prob
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    {s t : ℝ≥0} (hst : s ≤ t) (n : ℕ) :
    P.real {ω : Ω | H.intervalCount s t ω = n} =
      countLikelihood H.rate ((t : ℝ) - (s : ℝ)) n := by
  exact
    hasLaw_poissonMeasure_real_singleton_eq_countLikelihood
      (mul_nonneg H.rate_nonneg
        (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst)))
      (H.intervalCount_hasLaw hst) n

/--
At a forward time `t`, the count itself has the Poisson law at exposure `t`.
This uses the forward zero baseline only; it does not promote the model to a
two-sided stationary process.
-/
theorem count_hasLaw
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (t : ℝ≥0) :
    ProbabilityTheory.HasLaw
      (H.count t)
      (ProbabilityTheory.poissonMeasure
        (rateExposureParam H.rate (t : ℝ)
          (mul_nonneg H.rate_nonneg (NNReal.coe_nonneg t)))) P := by
  have hEq :
      (fun ω : Ω => H.count t ω) =ᵐ[P]
        (fun ω : Ω => H.count t ω - H.count 0 ω) := by
    filter_upwards [H.count_zero_ae] with ω hzero
    simp [hzero]
  simpa using (H.increment_hasLaw (s := 0) (t := t) (zero_le t)).congr hEq

/-- Real-valued Poisson PMF for the forward count at time `t`. -/
theorem count_prob
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (t : ℝ≥0) (n : ℕ) :
    P.real {ω : Ω | H.count t ω = n} =
      countLikelihood H.rate (t : ℝ) n := by
  exact
    hasLaw_poissonMeasure_real_singleton_eq_countLikelihood
      (mul_nonneg H.rate_nonneg (NNReal.coe_nonneg t))
      (H.count_hasLaw t) n

/--
The one-time count law in the unit-rate/mean form used by the M/M/1 mixture
calculation.  This is the direct bridge to a future service-count argument.
-/
theorem count_prob_eq_unit_rate_product
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (t : ℝ≥0) (n : ℕ) :
    P.real {ω : Ω | H.count t ω = n} =
      countLikelihood 1 (H.rate * (t : ℝ)) n := by
  rw [H.count_prob t n]
  simp [countLikelihood]

/--
At a real nonnegative horizon, the forward count has exactly the
unit-rate/mean form expected by the stationary M/M/1 mixture theorem.
-/
theorem count_prob_atReal_eq_unit_rate_product
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    P.real {ω : Ω | H.count z.toNNReal ω = n} =
      countLikelihood 1 (H.rate * z) n := by
  simpa [Real.coe_toNNReal _ hz] using
    H.count_prob_eq_unit_rate_product z.toNNReal n

/-- Independent forward interval counts along any monotone finite timeline. -/
theorem iIndepFun_intervalCount_fin
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    {n : ℕ} {t : Fin (n + 1) → ℝ≥0} (ht : Monotone t) :
    ProbabilityTheory.iIndepFun
      (fun (i : Fin n) (ω : Ω) =>
        H.intervalCount (t i.castSucc) (t i.succ) ω) P := by
  simpa [intervalCount] using H.hasIndepIncrements n t ht

/-- The count in the forward unit interval `[n,n+1]`. -/
def unitIntervalCount
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (n : ℕ) (omega : Ω) : ℕ :=
  H.intervalCount (n : ℝ≥0) ((n : ℝ≥0) + 1) omega

/-- Unit-width interval counts are measurable random variables. -/
theorem measurable_unitIntervalCount
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (n : ℕ) :
    Measurable (H.unitIntervalCount n) :=
  H.measurable_intervalCount _ _

/-- Every unit-width forward increment has the same Poisson law. -/
theorem unitIntervalCount_hasLaw
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (n : ℕ) :
    ProbabilityTheory.HasLaw (H.unitIntervalCount n)
      (ProbabilityTheory.poissonMeasure
        (rateExposureParam H.rate 1 (by simpa using H.rate_nonneg))) P := by
  have hle : (n : ℝ≥0) ≤ ((n + 1 : ℕ) : ℝ≥0) := by
    exact_mod_cast Nat.le_succ n
  simpa [unitIntervalCount] using H.intervalCount_hasLaw hle

/-- Unit-width forward increments are jointly independent. -/
theorem iIndepFun_unitIntervalCount
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P) :
    ProbabilityTheory.iIndepFun H.unitIntervalCount P := by
  simpa [unitIntervalCount, intervalCount] using
    H.hasIndepIncrements.nat (t := fun n : ℕ => (n : ℝ≥0)) (by
      intro i j hij
      change (i : ℝ≥0) ≤ (j : ℝ≥0)
      exact_mod_cast hij)

/-- Pairwise independence form used by the strong-law interface. -/
theorem pairwise_indepFun_unitIntervalCount
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P) :
    Pairwise (fun i j => ProbabilityTheory.IndepFun
      (H.unitIntervalCount i) (H.unitIntervalCount j) P) := by
  intro i j hij
  exact H.iIndepFun_unitIntervalCount.indepFun hij

/-- Unit-width forward increments are identically distributed. -/
theorem unitIntervalCount_identDistrib
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (n : ℕ) :
    ProbabilityTheory.IdentDistrib (H.unitIntervalCount n)
      (H.unitIntervalCount 0) P P :=
  (H.unitIntervalCount_hasLaw n).identDistrib
    (H.unitIntervalCount_hasLaw 0)

/-- The real-valued unit counts retain pairwise independence. -/
theorem pairwise_indepFun_unitIntervalCount_real
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P) :
    Pairwise (fun i j => ProbabilityTheory.IndepFun
      (fun omega => (H.unitIntervalCount i omega : ℝ))
      (fun omega => (H.unitIntervalCount j omega : ℝ)) P) := by
  intro i j hij
  simpa only [Function.comp_apply] using
    (H.pairwise_indepFun_unitIntervalCount hij).comp
      (measurable_of_countable fun n : ℕ => (n : ℝ))
      (measurable_of_countable fun n : ℕ => (n : ℝ))

/-- The real-valued unit counts retain their common distribution. -/
theorem unitIntervalCount_real_identDistrib
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (n : ℕ) :
    ProbabilityTheory.IdentDistrib
      (fun omega => (H.unitIntervalCount n omega : ℝ))
      (fun omega => (H.unitIntervalCount 0 omega : ℝ)) P P := by
  simpa only [Function.comp_apply] using
    (H.unitIntervalCount_identDistrib n).comp
      (measurable_of_countable fun k : ℕ => (k : ℝ))

/-- The real-valued first unit count is integrable. -/
theorem unitIntervalCount_real_integrable
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P) :
    Integrable (fun omega => (H.unitIntervalCount 0 omega : ℝ)) P := by
  let r : ℝ≥0 := rateExposureParam H.rate 1 (by simpa using H.rate_nonneg)
  have hint : Integrable (fun n : ℕ => (n : ℝ))
      (ProbabilityTheory.poissonMeasure r) :=
    integrable_natCast_poissonMeasure r
  have hmap : Integrable (fun n : ℕ => (n : ℝ))
      (Measure.map (H.unitIntervalCount 0) P) := by
    rw [(H.unitIntervalCount_hasLaw 0).map_eq]
    exact hint
  simpa [Function.comp_def] using
    hmap.comp_aemeasurable (H.unitIntervalCount_hasLaw 0).aemeasurable

/-- The expected count in a unit-width forward interval is the process rate. -/
theorem unitIntervalCount_real_expectation
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P) :
    ∫ omega, (H.unitIntervalCount 0 omega : ℝ) ∂P = H.rate := by
  let r : ℝ≥0 := rateExposureParam H.rate 1 (by simpa using H.rate_nonneg)
  calc
    ∫ omega, (H.unitIntervalCount 0 omega : ℝ) ∂P =
        ∫ n : ℕ, (n : ℝ) ∂ProbabilityTheory.poissonMeasure r := by
      simpa [r, Function.comp_def] using
        (H.unitIntervalCount_hasLaw 0).integral_comp
          (f := fun n : ℕ => (n : ℝ))
          (measurable_of_countable _).aestronglyMeasurable
    _ = r := integral_id_poissonMeasure r
    _ = H.rate := by
      change H.rate * 1 = H.rate
      ring

/-- Forward unit-interval counts obey the almost-sure strong law. -/
theorem unitIntervalCount_real_strongLaw
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P) :
    ∀ᵐ omega ∂P,
      Tendsto (fun n : ℕ =>
        (∑ i ∈ Finset.range n, (H.unitIntervalCount i omega : ℝ)) / n)
        atTop (nhds H.rate) := by
  have hsl := ProbabilityTheory.strong_law_ae_real
    (fun i omega => (H.unitIntervalCount i omega : ℝ))
    H.unitIntervalCount_real_integrable
    H.pairwise_indepFun_unitIntervalCount_real
    H.unitIntervalCount_real_identDistrib
  simpa [H.unitIntervalCount_real_expectation] using hsl

end ForwardHomogeneousPoissonCountingProcessByLaw

end

end PoissonProcess
end Probability
end EconCSLib
