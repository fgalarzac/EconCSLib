import EconCSLib.Foundations.Probability.ExponentialInterarrivalForwardPoisson
import EconCSLib.Foundations.Probability.ForwardPoissonTransport

/-!
# Independent finite-class forward Poisson input

This module constructs a finite family of independent forward homogeneous
Poisson processes on one product probability space.  Each class owns a full
interarrival path; independence is consequently an independence statement
about complete paths, not just about one selected count or a named wrapper.

It is the forward-input layer for finite-class queueing models.  It does not
make a stationarity, Palm, thinning, service-mark, or scheduling claim.
-/

namespace EconCSLib.Probability.PoissonProcess

open MeasureTheory Filter

noncomputable section

variable {Class : Type*} [Fintype Class]

/-- Product law carrying one canonical exponential-interarrival path for each
class of a finite queueing system. -/
def multiclassForwardArrivalMeasure (rate : Class → ℝ) :
    Measure (Class → ℕ → ℝ) :=
  Measure.pi fun i => exponentialInterarrivalMeasure (rate i)

/-- The finite-class product carrier is a probability space when every class
has a positive arrival rate. -/
theorem isProbabilityMeasure_multiclassForwardArrivalMeasure
    (rate : Class → ℝ) (hrate : ∀ i, 0 < rate i) :
    IsProbabilityMeasure (multiclassForwardArrivalMeasure rate) := by
  let μ : Class → Measure (ℕ → ℝ) :=
    fun i => exponentialInterarrivalMeasure (rate i)
  letI : ∀ i, IsProbabilityMeasure (μ i) := fun i =>
    isProbabilityMeasure_exponentialInterarrivalMeasure (hrate i)
  simpa [multiclassForwardArrivalMeasure, μ] using
    (inferInstance : IsProbabilityMeasure (Measure.pi μ))

/-- The concrete forward Poisson process of one class, carried by the joint
finite-class input space. -/
def multiclassForwardPoissonCountingProcess
    (rate : Class → ℝ) (hrate : ∀ i, 0 < rate i) (i : Class) :
    ForwardHomogeneousPoissonCountingProcessByLaw (Class → ℕ → ℝ)
      (multiclassForwardArrivalMeasure rate) := by
  let μ : Class → Measure (ℕ → ℝ) :=
    fun j => exponentialInterarrivalMeasure (rate j)
  letI : ∀ j, IsProbabilityMeasure (μ j) := fun j =>
    isProbabilityMeasure_exponentialInterarrivalMeasure (hrate j)
  simpa [multiclassForwardArrivalMeasure, μ] using
    (canonicalForwardHomogeneousPoissonCountingProcessByLaw (hrate i)).compMeasurePreserving
      (Function.eval i) (measurePreserving_eval μ i)

/-- The complete interarrival paths of the finite family are independent.
This is stronger than independence of any individual collection of count
increments and is the input-level independence needed by an eventual GPS
execution. -/
theorem iIndepFun_multiclassForwardArrivalPaths
    (rate : Class → ℝ) (hrate : ∀ i, 0 < rate i) :
    ProbabilityTheory.iIndepFun (fun i (ω : Class → ℕ → ℝ) => ω i)
      (multiclassForwardArrivalMeasure rate) := by
  let μ : Class → Measure (ℕ → ℝ) :=
    fun i => exponentialInterarrivalMeasure (rate i)
  letI : ∀ i, IsProbabilityMeasure (μ i) := fun i =>
    isProbabilityMeasure_exponentialInterarrivalMeasure (hrate i)
  simpa [multiclassForwardArrivalMeasure, μ] using
    (ProbabilityTheory.iIndepFun_pi (X := fun _ : Class => id)
      (fun _ => aemeasurable_id))

/-- The finite set of forward arrival indices of one class by a finite time.
It is defined from the concrete renewal path, not inferred from a count law. -/
noncomputable def multiclassForwardArrivalIndices
    (i : Class) (t : ℝ) (ω : Class → ℕ → ℝ) : Finset ℕ :=
  Finset.range (canonicalRenewalCount t (ω i))

/-- On the joint finite-class carrier, each local arrival ledger enumerates
exactly the arrivals of its class that have occurred by its horizon.  The
simultaneous quantifiers are important: this is a finite-class path property,
not a collection of unrelated fixed-time marginal statements. -/
theorem ae_mem_multiclassForwardArrivalIndices_iff
    (rate : Class → ℝ) (hrate : ∀ i, 0 < rate i) :
    ∀ᵐ ω ∂multiclassForwardArrivalMeasure rate, ∀ i : Class, ∀ t : ℝ, ∀ n : ℕ,
      n ∈ multiclassForwardArrivalIndices i t ω ↔ arrivalTime n (ω i) ≤ t := by
  let μ : Class → Measure (ℕ → ℝ) :=
    fun i => exponentialInterarrivalMeasure (rate i)
  letI : ∀ i, IsProbabilityMeasure (μ i) := fun i =>
    isProbabilityMeasure_exponentialInterarrivalMeasure (hrate i)
  rw [ae_all_iff]
  intro i
  have hcoordinate : ∀ᵐ ω ∂Measure.pi μ, ∀ t : ℝ, ∀ n : ℕ,
      n < canonicalRenewalCount t (ω i) ↔ arrivalTime n (ω i) ≤ t := by
    refine ae_of_ae_map (μ := Measure.pi μ) (f := Function.eval i)
      (p := fun ξ : ℕ → ℝ => ∀ t : ℝ, ∀ n : ℕ,
        n < canonicalRenewalCount t ξ ↔ arrivalTime n ξ ≤ t)
      (measurePreserving_eval μ i).measurable.aemeasurable ?_
    rw [(measurePreserving_eval μ i).map_eq]
    exact ae_lt_canonicalRenewalCount_iff_arrivalTime_le (hrate i)
  simpa [multiclassForwardArrivalMeasure, μ, multiclassForwardArrivalIndices,
    Finset.mem_range] using hcoordinate

/-- Every class path in the joint finite-class carrier is nonexplosive and
strictly ordered almost surely.  Together with the finite ledger above, this
is the path-level local-finiteness fact needed before an event-driven scheduler
can be defined. -/
theorem ae_multiclassForwardArrivalPaths_nonexplosive_strict
    (rate : Class → ℝ) (hrate : ∀ i, 0 < rate i) :
    ∀ᵐ ω ∂multiclassForwardArrivalMeasure rate, ∀ i : Class,
      Tendsto (fun n : ℕ => arrivalTime n (ω i)) atTop atTop ∧
        StrictMono (fun n : ℕ => arrivalTime n (ω i)) := by
  let μ : Class → Measure (ℕ → ℝ) :=
    fun i => exponentialInterarrivalMeasure (rate i)
  letI : ∀ i, IsProbabilityMeasure (μ i) := fun i =>
    isProbabilityMeasure_exponentialInterarrivalMeasure (hrate i)
  rw [ae_all_iff]
  intro i
  refine ae_of_ae_map (μ := Measure.pi μ) (f := Function.eval i)
    (p := fun ξ : ℕ → ℝ =>
      Tendsto (fun n : ℕ => arrivalTime n ξ) atTop atTop ∧
        StrictMono (fun n : ℕ => arrivalTime n ξ))
    (measurePreserving_eval μ i).measurable.aemeasurable ?_
  rw [(measurePreserving_eval μ i).map_eq]
  exact (ae_arrivalTime_tendsto_atTop (hrate i)).and
    (ae_arrivalTime_strictMono (hrate i))

/-- On the same good carrier, each class has a strictly later next arrival at
every finite time.  An event scheduler can therefore advance past a current
time even when it batches ties across classes. -/
theorem ae_multiclassForward_nextArrival_gt
    (rate : Class → ℝ) (hrate : ∀ i, 0 < rate i) :
    ∀ᵐ ω ∂multiclassForwardArrivalMeasure rate, ∀ i : Class, ∀ t : ℝ,
      t < arrivalTime (canonicalRenewalCount t (ω i)) (ω i) := by
  filter_upwards [ae_multiclassForwardArrivalPaths_nonexplosive_strict rate hrate]
    with ω hgood
  intro i t
  exact lt_arrivalTime_canonicalRenewalCount t (ω i)
    (exists_arrivalTime_gt_of_tendsto_atTop (ω i) (hgood i).1 t)

omit [Fintype Class] in
/-- The local arrival ledger is finite by construction, with its cardinality
equal to the concrete renewal count. -/
theorem multiclassForwardArrivalIndices_card
    (i : Class) (t : ℝ) (ω : Class → ℕ → ℝ) :
    (multiclassForwardArrivalIndices i t ω).card =
      canonicalRenewalCount t (ω i) := by
  simp [multiclassForwardArrivalIndices]

end

end EconCSLib.Probability.PoissonProcess
