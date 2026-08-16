import EconCSLib.Foundations.Probability.ExponentialInterarrivalRenewalRate
import EconCSLib.Foundations.Probability.MulticlassQueueingPrimitives
import Mathlib.Tactic

/-!
# Work rate of a marked canonical exponential renewal input

This module records only an input-process law of large numbers.  A canonical
rate-`rate` exponential renewal path is paired with an independent canonical
unit-exponential work-mark path, and cumulative work means the sum of marks
whose arrival indices are strictly before the canonical renewal count at the
specified time.  It does not introduce a queue, service discipline, reset, or
stability claim.
-/

namespace EconCSLib.Probability.PoissonProcess

open MeasureTheory Filter Finset
open scoped Topology ProbabilityTheory Function NNReal

noncomputable section

/-- Total work of the arrivals counted by the canonical renewal count before
time `t`.  The half-open convention is inherited from `canonicalRenewalCount`:
an arrival at exactly `t` is included when the count construction includes it. -/
def canonicalMarkedWork
    (arrivalGaps workMarks : Nat -> Real) (t : Real) : Real :=
  (Finset.range (canonicalRenewalCount t arrivalGaps)).sum
    fun n => interarrival n workMarks

/-- A deterministic random-index composition lemma for marked renewal input.
The first hypothesis is the time-indexed renewal-count rate; the second says
that the count itself tends to infinity, and the third is the ordinary
empirical-mean law for the marks. -/
theorem tendsto_canonicalMarkedWork_div_atTop_of_tendsto
    {rate : Real} (arrivalGaps workMarks : Nat -> Real)
    (hcount : Tendsto
      (fun t : Real => (canonicalRenewalCount t arrivalGaps : Real) / t)
      atTop (nhds rate))
    (hcount_atTop : Tendsto
      (fun t : Real => canonicalRenewalCount t arrivalGaps)
      atTop atTop)
    (hmarks : Tendsto
      (fun n : Nat =>
        (Finset.range n).sum (fun i => interarrival i workMarks) / n)
      atTop (nhds 1)) :
    Tendsto
      (fun t : Real => canonicalMarkedWork arrivalGaps workMarks t / t)
      atTop (nhds rate) := by
  have hmarks_at_count : Tendsto
      (fun t : Real =>
        (Finset.range (canonicalRenewalCount t arrivalGaps)).sum
          (fun i => interarrival i workMarks) /
          (canonicalRenewalCount t arrivalGaps : Real))
      atTop (nhds 1) :=
    hmarks.comp hcount_atTop
  have hprod := hmarks_at_count.mul hcount
  have heq :
      (fun t : Real =>
        ((Finset.range (canonicalRenewalCount t arrivalGaps)).sum
          (fun i => interarrival i workMarks) /
          (canonicalRenewalCount t arrivalGaps : Real)) *
          ((canonicalRenewalCount t arrivalGaps : Real) / t)) =ᶠ[atTop]
      fun t => canonicalMarkedWork arrivalGaps workMarks t / t := by
    filter_upwards [hcount_atTop.eventually (eventually_ge_atTop 1)] with t ht
    have hcount_ne : (canonicalRenewalCount t arrivalGaps : Real) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (by omega : 0 < canonicalRenewalCount t arrivalGaps))
    simp only [canonicalMarkedWork]
    field_simp [hcount_ne]
  simpa using hprod.congr' heq

/-- If canonical arrival epochs diverge and are monotone, then their canonical
renewal count tends to infinity as real time tends to infinity. -/
theorem tendsto_canonicalRenewalCount_atTop_of_arrivalTime_tendsto
    (arrivalGaps : Nat -> Real)
    (harrival : Tendsto (fun n : Nat => arrivalTime n arrivalGaps) atTop atTop)
    (hmono : Monotone (fun n : Nat => arrivalTime n arrivalGaps)) :
    Tendsto (fun t : Real => canonicalRenewalCount t arrivalGaps) atTop atTop := by
  refine tendsto_atTop.2 fun n => ?_
  exact (eventually_ge_atTop (arrivalTime n arrivalGaps)).mono fun t ht =>
    Nat.le_of_lt
      ((lt_canonicalRenewalCount_iff_arrivalTime_le_of_tendsto arrivalGaps
        harrival hmono t n).mpr ht)

/-- The concrete product carrier of a canonical exponential renewal path and
an independent canonical unit-exponential work-mark path. -/
def exponentialMarkedRenewalWorkMeasure (rate : Real) :
    Measure ((Nat -> Real) × (Nat -> Real)) :=
  (exponentialInterarrivalMeasure rate).prod (exponentialInterarrivalMeasure 1)

/-- The marked renewal product is a probability law at positive arrival rate. -/
theorem isProbabilityMeasure_exponentialMarkedRenewalWorkMeasure
    {rate : Real} (hrate : 0 < rate) :
    IsProbabilityMeasure (exponentialMarkedRenewalWorkMeasure rate) := by
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure (1 : Real)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  simpa [exponentialMarkedRenewalWorkMeasure] using
    (inferInstance : IsProbabilityMeasure
      ((exponentialInterarrivalMeasure rate).prod (exponentialInterarrivalMeasure 1)))

/-- The empirical mean of the canonical unit-exponential work-mark path
converges almost surely to one.  This is the work-mark half of the marked
renewal input, before it is evaluated at a random arrival count. -/
theorem ae_tendsto_unitExponentialWorkMark_mean :
    ∀ᵐ workMarks ∂exponentialInterarrivalMeasure (1 : Real),
      Tendsto
        (fun n : Nat =>
          (Finset.range n).sum (fun i => interarrival i workMarks) / n)
        atTop (nhds 1) := by
  have hindep : Pairwise
      ((· ⟂ᵢ[exponentialInterarrivalMeasure (1 : Real)] ·) on interarrival) := by
    intro i j hij
    exact (iIndepFun_interarrival (by norm_num : 0 < (1 : Real))).indepFun hij
  have hident : ∀ i, ProbabilityTheory.IdentDistrib (interarrival i) (interarrival 0)
      (exponentialInterarrivalMeasure (1 : Real))
      (exponentialInterarrivalMeasure (1 : Real)) :=
    fun i => (interarrival_hasLaw (by norm_num : 0 < (1 : Real)) i).identDistrib
      (interarrival_hasLaw (by norm_num : 0 < (1 : Real)) 0)
  have hmean : (exponentialInterarrivalMeasure (1 : Real))[interarrival 0] = 1 := by
    simpa using integral_interarrival_zero_eq_inv_rate (rate := (1 : Real))
      (by norm_num)
  simpa [hmean] using
    (ProbabilityTheory.strong_law_ae_real interarrival
      (integrable_interarrival_zero (by norm_num : 0 < (1 : Real))) hindep hident)

/-- Combine the four source-input almost-sure facts needed for the marked
work-rate law.  This deliberately has no independence premise: independence
is used to construct the source carrier, while the conclusion only needs the
two verified marginal full-measure facts simultaneously. -/
theorem ae_tendsto_canonicalMarkedWork_div_atTop_of_ae_inputs
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} {rate : Real}
    (arrivalGaps workMarks : Omega -> Nat -> Real)
    (hcount : ∀ᵐ omega ∂P,
      Tendsto
        (fun t : Real => (canonicalRenewalCount t (arrivalGaps omega) : Real) / t)
        atTop (nhds rate))
    (harrival : ∀ᵐ omega ∂P,
      Tendsto (fun n : Nat => arrivalTime n (arrivalGaps omega)) atTop atTop)
    (hmono : ∀ᵐ omega ∂P,
      Monotone (fun n : Nat => arrivalTime n (arrivalGaps omega)))
    (hmarks : ∀ᵐ omega ∂P,
      Tendsto
        (fun n : Nat =>
          (Finset.range n).sum (fun i => interarrival i (workMarks omega)) / n)
        atTop (nhds 1)) :
    ∀ᵐ omega ∂P,
      Tendsto
        (fun t : Real =>
          canonicalMarkedWork (arrivalGaps omega) (workMarks omega) t / t)
        atTop (nhds rate) := by
  filter_upwards [hcount, harrival, hmono, hmarks]
    with omega hcount harrival hmono hmarks
  exact tendsto_canonicalMarkedWork_div_atTop_of_tendsto
    (arrivalGaps omega) (workMarks omega) hcount
    (tendsto_canonicalRenewalCount_atTop_of_arrivalTime_tendsto
      (arrivalGaps omega) harrival hmono)
    hmarks

/-- Transport the marked work-rate law through separately measure-preserving
arrival and work-mark coordinates.  This applies directly to source carriers
that expose the actual arrival and work paths as marginal factors. -/
theorem ae_tendsto_canonicalMarkedWork_div_atTop_of_marginal_measurePreserving
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} {rate : Real}
    (hrate : 0 < rate) (arrivalGaps workMarks : Omega -> Nat -> Real)
    (harrivalMeasure : MeasurePreserving arrivalGaps P
      (exponentialInterarrivalMeasure rate))
    (hworkMeasure : MeasurePreserving workMarks P
      (exponentialInterarrivalMeasure 1)) :
    ∀ᵐ omega ∂P,
      Tendsto
        (fun t : Real =>
          canonicalMarkedWork (arrivalGaps omega) (workMarks omega) t / t)
        atTop (nhds rate) := by
  have harrivalInput : ∀ᵐ arrivalGaps ∂exponentialInterarrivalMeasure rate,
      Tendsto
          (fun t : Real => (canonicalRenewalCount t arrivalGaps : Real) / t)
          atTop (nhds rate) ∧
        Tendsto (fun n : Nat => arrivalTime n arrivalGaps) atTop atTop ∧
        Monotone (fun n : Nat => arrivalTime n arrivalGaps) :=
    (ae_tendsto_canonicalRenewalCount_div_atTop hrate).and
      ((ae_arrivalTime_tendsto_atTop hrate).and (ae_arrivalTime_monotone hrate))
  have harrivalLift : ∀ᵐ omega ∂P,
      Tendsto
          (fun t : Real =>
            (canonicalRenewalCount t (arrivalGaps omega) : Real) / t)
          atTop (nhds rate) ∧
        Tendsto (fun n : Nat => arrivalTime n (arrivalGaps omega)) atTop atTop ∧
        Monotone (fun n : Nat => arrivalTime n (arrivalGaps omega)) := by
    refine ae_of_ae_map (μ := P) (f := arrivalGaps)
      (p := fun arrivalGaps : Nat -> Real =>
        Tendsto
            (fun t : Real => (canonicalRenewalCount t arrivalGaps : Real) / t)
            atTop (nhds rate) ∧
          Tendsto (fun n : Nat => arrivalTime n arrivalGaps) atTop atTop ∧
          Monotone (fun n : Nat => arrivalTime n arrivalGaps))
      harrivalMeasure.measurable.aemeasurable ?_
    rw [harrivalMeasure.map_eq]
    exact harrivalInput
  have hworkLift : ∀ᵐ omega ∂P,
      Tendsto
        (fun n : Nat =>
          (Finset.range n).sum (fun i => interarrival i (workMarks omega)) / n)
        atTop (nhds 1) := by
    refine ae_of_ae_map (μ := P) (f := workMarks)
      (p := fun workMarks : Nat -> Real =>
        Tendsto
          (fun n : Nat =>
            (Finset.range n).sum (fun i => interarrival i workMarks) / n)
          atTop (nhds 1))
      hworkMeasure.measurable.aemeasurable ?_
    rw [hworkMeasure.map_eq]
    exact ae_tendsto_unitExponentialWorkMark_mean
  filter_upwards [harrivalLift, hworkLift]
    with omega harrival hwork
  exact tendsto_canonicalMarkedWork_div_atTop_of_tendsto
    (arrivalGaps omega) (workMarks omega) harrival.1
    (tendsto_canonicalRenewalCount_atTop_of_arrivalTime_tendsto
      (arrivalGaps omega) harrival.2.1 harrival.2.2)
    hwork

/-- On the explicit independent product of a rate-`rate` canonical arrival
path and iid unit-exponential work marks, marked cumulative input work has
almost-sure long-run rate `rate`.  This is only a primitive input law. -/
theorem ae_tendsto_canonicalMarkedWork_div_atTop
    {rate : Real} (hrate : 0 < rate) :
    ∀ᵐ omega ∂exponentialMarkedRenewalWorkMeasure rate,
      Tendsto
        (fun t : Real => canonicalMarkedWork omega.1 omega.2 t / t)
        atTop (nhds rate) := by
  let μa : Measure (Nat -> Real) := exponentialInterarrivalMeasure rate
  let μw : Measure (Nat -> Real) := exponentialInterarrivalMeasure 1
  letI : IsProbabilityMeasure μa :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure μw :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  change ∀ᵐ omega : (Nat -> Real) × (Nat -> Real) ∂μa.prod μw,
    Tendsto
      (fun t : Real => canonicalMarkedWork omega.1 omega.2 t / t)
      atTop (nhds rate)
  exact ae_tendsto_canonicalMarkedWork_div_atTop_of_marginal_measurePreserving
    hrate Prod.fst Prod.snd measurePreserving_fst measurePreserving_snd

variable {Class : Type*} [Fintype Class]

/-- The actual arrival/work coordinates of one class in the reusable finite
class primitive carrier have their marked-work rate.  The theorem uses those
same source coordinates, not an independently substituted Poisson process. -/
theorem ae_tendsto_multiclassPrimitiveMarkedWork_div_atTop
    (arrivalRate : Class -> Real) (harrivalRate : ∀ i, 0 < arrivalRate i)
    (admissionProbability : Class -> ℝ≥0)
    (hadmissionProbability : ∀ i, admissionProbability i ≤ 1) (i : Class) :
    ∀ᵐ omega ∂multiclassForwardQueueingPrimitiveMeasure arrivalRate
      admissionProbability hadmissionProbability,
      Tendsto
        (fun t : Real =>
          canonicalMarkedWork
            (multiclassForwardQueueingPrimitiveRawInterarrivals i omega)
            (multiclassForwardQueueingPrimitiveWorkMarks i omega) t / t)
        atTop (nhds (arrivalRate i)) := by
  exact ae_tendsto_canonicalMarkedWork_div_atTop_of_marginal_measurePreserving
    (harrivalRate i)
    (multiclassForwardQueueingPrimitiveRawInterarrivals i)
    (multiclassForwardQueueingPrimitiveWorkMarks i)
    (measurePreserving_multiclassPrimitiveRawInterarrivals arrivalRate harrivalRate
      admissionProbability hadmissionProbability i)
    (measurePreserving_multiclassPrimitiveWorkMarks arrivalRate harrivalRate
      admissionProbability hadmissionProbability i)

end

end EconCSLib.Probability.PoissonProcess
