import EconCSLib.Foundations.Probability.ForwardPoisson
import EconCSLib.Foundations.Probability.QueueingMM1TrajectoryTimeChange

/-!
# External forward-Poisson time changes of stationary embedded trajectories

This construction puts an invariant embedded Markov trajectory and an
external forward Poisson count path on a product probability space.  At each
fixed time the time-changed state has the invariant marginal, and its
initial/current pair is an explicit Poisson mixture of embedded transition
laws.  These are only product-space fixed-time statements: they do not
identify a CTMC semigroup, prove càdlàg paths, or construct a Palm law.  In
particular, the joint fixed-time laws below do not identify actual marked
arrival or potential-service clocks, prove marked thinning, establish PASTA,
or select a stationary/Palm-tagged arrival.
-/

namespace EconCSLib.Probability.Queueing

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- Evaluate an embedded trajectory at the count of an external forward
Poisson clock.  The product space makes the clock independent of the
trajectory by construction. -/
def stationaryTrajectoryAtForwardPoissonCount
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (t : ℝ≥0) : ((ℕ → α) × Ω) → α :=
  fun z => z.1 (H.count t z.2)

theorem measurable_stationaryTrajectoryAtForwardPoissonCount
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (t : ℝ≥0) :
    Measurable (stationaryTrajectoryAtForwardPoissonCount (α := α) H t) := by
  simpa [stationaryTrajectoryAtForwardPoissonCount] using
    measurable_trajectoryAtIndependentRandomIndex (α := α)
      (H.count t) (H.measurable_count t)

/-- Fixed-time marginal law for an invariant embedded chain independently
time-changed by a forward Poisson counting path.  This does not assert the
continuous-time Markov semigroup or a Palm construction. -/
theorem stationaryTrajMeasure_eval_forwardPoissonCount_hasLaw
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    (hstationary : Kernel.Invariant K π)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (t : ℝ≥0) :
    HasLaw (stationaryTrajectoryAtForwardPoissonCount (α := α) H t) π
      ((stationaryTrajMeasure π K).prod P) := by
  letI : IsProbabilityMeasure P := H.isProbability
  simpa [stationaryTrajectoryAtForwardPoissonCount] using
    stationaryTrajMeasure_eval_independentRandomIndex_hasLaw
      hstationary (H.count t) (H.measurable_count t)

/-- At a fixed deterministic time, an invariant embedded state evaluated at
an external forward-Poisson count is jointly independent of that count.  This
uses the product-space external clock only; it does not identify a CTMC,
marked arrival/service thinning, PASTA, or a Palm-tagged arrival. -/
theorem stationaryTrajMeasure_eval_forwardPoissonCount_joint_hasLaw
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    (hstationary : Kernel.Invariant K π)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (t : ℝ≥0) :
    HasLaw
      (fun z : (ℕ → α) × Ω =>
        (stationaryTrajectoryAtForwardPoissonCount (α := α) H t z, H.count t z.2))
      (π.prod (ProbabilityTheory.poissonMeasure
        (PoissonProcess.rateExposureParam H.rate (t : ℝ)
          (mul_nonneg H.rate_nonneg (NNReal.coe_nonneg t)))))
      ((stationaryTrajMeasure π K).prod P) := by
  letI : IsProbabilityMeasure P := H.isProbability
  letI : IsProbabilityMeasure (stationaryTrajMeasure π K) := by
    unfold stationaryTrajMeasure
    infer_instance
  let h := stationaryTrajMeasure_eval_independentRandomIndex_joint_hasLaw
    (π := π) (K := K) (P := P)
    hstationary (H.count t) (H.measurable_count t)
  refine ⟨?_, ?_⟩
  · simpa [stationaryTrajectoryAtForwardPoissonCount] using h.aemeasurable
  · calc
      Measure.map
          (fun z : (ℕ → α) × Ω =>
            (stationaryTrajectoryAtForwardPoissonCount (α := α) H t z, H.count t z.2))
          ((stationaryTrajMeasure π K).prod P) =
          π.prod (P.map (H.count t)) := by
            simpa [stationaryTrajectoryAtForwardPoissonCount] using h.map_eq
      _ = π.prod (ProbabilityTheory.poissonMeasure
          (PoissonProcess.rateExposureParam H.rate (t : ℝ)
            (mul_nonneg H.rate_nonneg (NNReal.coe_nonneg t)))) := by
            rw [(H.count_hasLaw t).map_eq]

/-- Under the product law of an embedded trajectory and a forward Poisson
clock, the initial/current pair is the Poisson mixture of the `n`-jump pair
laws.  The result uses external-clock independence only; it does not make the
initial state a stationary/Palm tagged arrival or identify a response-time
tail. -/
theorem stationaryTrajMeasure_zero_forwardPoissonCount_pair_mixture
    {π : Measure α} [IsProbabilityMeasure π] {K : Kernel α α} [IsMarkovKernel K]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (t : ℝ≥0) (s : Set (α × α)) (hs : MeasurableSet s) :
    ((stationaryTrajMeasure π K).prod P).map
        (fun z : (ℕ → α) × Ω => (z.1 0, z.1 (H.count t z.2))) s =
      ∫⁻ n, (π ⊗ₘ (K ^ n)) s ∂
        ProbabilityTheory.poissonMeasure
          (PoissonProcess.rateExposureParam H.rate (t : ℝ)
            (mul_nonneg H.rate_nonneg (NNReal.coe_nonneg t))) := by
  letI : IsProbabilityMeasure P := H.isProbability
  simpa only [(H.count_hasLaw t).map_eq] using
    (stationaryTrajMeasure_zero_externalIndex_pair_mixture
      (π := π) (K := K) (P := P) (H.count t) (H.measurable_count t) s hs)

/-- The rate-specialized uniformized M/M/1 embedded trajectory retains its
geometric state law after an independent external forward Poisson time change
at every fixed time.  The conclusion deliberately does not identify the
resulting process as a CTMC semigroup. -/
theorem mm1_uniformized_stationaryTraj_eval_forwardPoissonCount_hasLaw
    (arrivalRate serviceRate : ℝ≥0) (hstable : arrivalRate < serviceRate)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (t : ℝ≥0) :
    HasLaw (stationaryTrajectoryAtForwardPoissonCount (α := ℕ) H t)
      (geoNNPMF (mm1TrafficIntensityNN arrivalRate serviceRate)
        (mm1TrafficIntensityNN_lt_one hstable)).toMeasure
      ((stationaryTrajMeasure
        (geoNNPMF (mm1TrafficIntensityNN arrivalRate serviceRate)
          (mm1TrafficIntensityNN_lt_one hstable)).toMeasure
        (countablePMFKernel
          (reflectedBirthDeathKernel
            (arrivalRate / (arrivalRate + serviceRate))
            (rate_fraction_le_one arrivalRate serviceRate)))).prod P) := by
  exact stationaryTrajMeasure_eval_forwardPoissonCount_hasLaw
    (mm1_uniformized_geometric_stationary arrivalRate serviceRate hstable).kernelInvariant H t

/-- At every deterministic time, the stationary uniformized M/M/1 state has
its geometric law jointly independently of the total external Poisson event
count.  This is a fixed-time invariance bridge only: it does not split total
events into actual arrivals and potential-service attempts, prove PASTA, or
construct a Palm-tagged arrival. -/
theorem mm1_uniformized_stationaryTraj_eval_forwardPoissonCount_joint_hasLaw
    (arrivalRate serviceRate : ℝ≥0) (hstable : arrivalRate < serviceRate)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (t : ℝ≥0) :
    HasLaw
      (fun z : (ℕ → ℕ) × Ω =>
        (stationaryTrajectoryAtForwardPoissonCount (α := ℕ) H t z, H.count t z.2))
      (((geoNNPMF (mm1TrafficIntensityNN arrivalRate serviceRate)
        (mm1TrafficIntensityNN_lt_one hstable)).toMeasure).prod
        (ProbabilityTheory.poissonMeasure
          (PoissonProcess.rateExposureParam H.rate (t : ℝ)
            (mul_nonneg H.rate_nonneg (NNReal.coe_nonneg t)))))
      ((stationaryTrajMeasure
        (geoNNPMF (mm1TrafficIntensityNN arrivalRate serviceRate)
          (mm1TrafficIntensityNN_lt_one hstable)).toMeasure
        (countablePMFKernel
          (reflectedBirthDeathKernel
            (arrivalRate / (arrivalRate + serviceRate))
            (rate_fraction_le_one arrivalRate serviceRate)))).prod P) := by
  exact stationaryTrajMeasure_eval_forwardPoissonCount_joint_hasLaw
    (mm1_uniformized_geometric_stationary arrivalRate serviceRate hstable).kernelInvariant H t

/-- The preceding fixed-time joint law when the external event clock is
rate-aligned with uniformization.  Its count parameter is literally
`(arrivalRate + serviceRate) * t`; this still does not identify marked
arrival/service clocks, PASTA, or a Palm-tagged arrival. -/
theorem mm1_uniformized_stationaryTraj_eval_alignedForwardPoissonCount_joint_hasLaw
    (arrivalRate serviceRate : ℝ≥0) (hstable : arrivalRate < serviceRate)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (hclockRate : H.rate = ((arrivalRate + serviceRate : ℝ≥0) : ℝ))
    (t : ℝ≥0) :
    HasLaw
      (fun z : (ℕ → ℕ) × Ω =>
        (stationaryTrajectoryAtForwardPoissonCount (α := ℕ) H t z, H.count t z.2))
      (((geoNNPMF (mm1TrafficIntensityNN arrivalRate serviceRate)
        (mm1TrafficIntensityNN_lt_one hstable)).toMeasure).prod
        (ProbabilityTheory.poissonMeasure
          (PoissonProcess.rateExposureParam
            ((arrivalRate + serviceRate : ℝ≥0) : ℝ) (t : ℝ)
            (mul_nonneg (by positivity) (NNReal.coe_nonneg t)))))
      ((stationaryTrajMeasure
        (geoNNPMF (mm1TrafficIntensityNN arrivalRate serviceRate)
          (mm1TrafficIntensityNN_lt_one hstable)).toMeasure
        (countablePMFKernel
          (reflectedBirthDeathKernel
            (arrivalRate / (arrivalRate + serviceRate))
            (rate_fraction_le_one arrivalRate serviceRate)))).prod P) := by
  simpa [hclockRate] using
    (mm1_uniformized_stationaryTraj_eval_forwardPoissonCount_joint_hasLaw
      arrivalRate serviceRate hstable H t)

/-- If the external clock is rate-aligned with the M/M/1 uniformization rate,
its fixed-time count has the expected Poisson parameter `(λ + μ)t`.  Together
with the preceding state-law theorem, this is the checked fixed-time
uniformization bridge; it is not a proof of a continuous-time semigroup. -/
theorem mm1_uniformization_forwardClock_count_hasLaw
    (arrivalRate serviceRate : ℝ≥0)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : PoissonProcess.ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (hclockRate : H.rate = ((arrivalRate + serviceRate : ℝ≥0) : ℝ))
    (t : ℝ≥0) :
    HasLaw (H.count t)
      (ProbabilityTheory.poissonMeasure
        (PoissonProcess.rateExposureParam
          ((arrivalRate + serviceRate : ℝ≥0) : ℝ) (t : ℝ)
          (mul_nonneg (by positivity) (NNReal.coe_nonneg t)))) P := by
  simpa [hclockRate] using H.count_hasLaw t

end

end EconCSLib.Probability.Queueing
