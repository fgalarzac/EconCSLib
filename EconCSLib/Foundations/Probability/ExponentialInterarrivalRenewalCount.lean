import EconCSLib.Foundations.Probability.ExponentialInterarrivalNonexplosion

/-!
# Canonical renewal count on the exponential interarrival path

This module turns the nonexplosive finite arrival epochs into a measurable
one-sided renewal count.  It proves its exact threshold/cardinality identities
on divergent monotone paths and supplies the natural adapted filtration.  It
does not yet prove Poisson increment laws or a continuous-time strong Markov
theorem for that count.
-/

namespace EconCSLib
namespace Probability
namespace PoissonProcess

open MeasureTheory Filter Finset
open scoped ENNReal NNReal Topology ProbabilityTheory Function

noncomputable section

/--
The one-sided renewal count associated with the canonical interarrival path.
It is the least arrival index strictly after `t`, hence counts the arrival
epochs `arrivalTime 0, arrivalTime 1, ...` that have occurred by `t` whenever
the arrival sequence eventually exceeds `t`.

The fallback value on an explosive/nonterminating path is immaterial for the
canonical exponential law, where nonexplosion holds almost surely.
-/
noncomputable def canonicalRenewalCount (t : ℝ) : (ℕ → ℝ) → ℕ := by
  classical
  exact fun ω => if h : ∃ n : ℕ, t < arrivalTime n ω then Nat.find h else 0

/-- On a path with a future arrival epoch after `t`, the renewal count is its
least such index. -/
theorem canonicalRenewalCount_eq_find
    (t : ℝ) (ω : ℕ → ℝ) (h : ∃ n : ℕ, t < arrivalTime n ω) :
    canonicalRenewalCount t ω = Nat.find h := by
  classical
  simp [canonicalRenewalCount, h]

/-- The count index is an arrival epoch strictly after `t`. -/
theorem lt_arrivalTime_canonicalRenewalCount
    (t : ℝ) (ω : ℕ → ℝ) (h : ∃ n : ℕ, t < arrivalTime n ω) :
    t < arrivalTime (canonicalRenewalCount t ω) ω := by
  rw [canonicalRenewalCount_eq_find t ω h]
  exact Nat.find_spec h

/-- Every strictly earlier index is an arrival that has already occurred by `t`. -/
theorem arrivalTime_le_of_lt_canonicalRenewalCount
    (t : ℝ) (ω : ℕ → ℝ) (h : ∃ n : ℕ, t < arrivalTime n ω)
    {n : ℕ} (hn : n < canonicalRenewalCount t ω) :
    arrivalTime n ω ≤ t := by
  rw [canonicalRenewalCount_eq_find t ω h] at hn
  exact le_of_not_gt (Nat.find_min h hn)

/-- If finite arrival epochs are monotone, an epoch has occurred exactly when
its index lies below the canonical renewal count. -/
theorem lt_canonicalRenewalCount_iff_arrivalTime_le
    (t : ℝ) (ω : ℕ → ℝ)
    (hfuture : ∃ n : ℕ, t < arrivalTime n ω)
    (hmono : Monotone (fun n : ℕ => arrivalTime n ω))
    (n : ℕ) :
    n < canonicalRenewalCount t ω ↔ arrivalTime n ω ≤ t := by
  constructor
  · exact arrivalTime_le_of_lt_canonicalRenewalCount t ω hfuture
  · intro hn
    by_contra hnot
    have hcount_le : canonicalRenewalCount t ω ≤ n := Nat.le_of_not_gt hnot
    have htime_le : arrivalTime (canonicalRenewalCount t ω) ω ≤ arrivalTime n ω :=
      hmono hcount_le
    exact (not_le_of_gt (lt_arrivalTime_canonicalRenewalCount t ω hfuture))
      (htime_le.trans hn)

/-- The canonical renewal count is exactly the cardinality of the completed
arrival indices, provided that a future arrival exists and the epochs are
monotone. -/
theorem canonicalRenewalCount_eq_ncard_completed
    (t : ℝ) (ω : ℕ → ℝ)
    (hfuture : ∃ n : ℕ, t < arrivalTime n ω)
    (hmono : Monotone (fun n : ℕ => arrivalTime n ω)) :
    canonicalRenewalCount t ω =
      ({n : ℕ | arrivalTime n ω ≤ t} : Set ℕ).ncard := by
  let k := canonicalRenewalCount t ω
  have hset : {n : ℕ | arrivalTime n ω ≤ t} = (Finset.range k : Set ℕ) := by
    ext n
    simpa [Finset.mem_range, k] using
      (lt_canonicalRenewalCount_iff_arrivalTime_le t ω hfuture hmono n).symm
  calc
    canonicalRenewalCount t ω = k := rfl
    _ = (Finset.range k).card := (Finset.card_range k).symm
    _ = (Finset.range k : Set ℕ).ncard := (Set.ncard_coe_finset _).symm
    _ = ({n : ℕ | arrivalTime n ω ≤ t} : Set ℕ).ncard := by rw [hset]

/-- An eventual divergence certificate supplies a future arrival after every
fixed time. -/
theorem exists_arrivalTime_gt_of_tendsto_atTop
    (ω : ℕ → ℝ)
    (hω : Tendsto (fun n : ℕ => arrivalTime n ω) atTop atTop)
    (t : ℝ) :
    ∃ n : ℕ, t < arrivalTime n ω := by
  exact (hω.eventually_gt_atTop t).exists

/-- On a nonexplosive monotone path, the renewal-count threshold identity
holds at every time and index. -/
theorem lt_canonicalRenewalCount_iff_arrivalTime_le_of_tendsto
    (ω : ℕ → ℝ)
    (hω : Tendsto (fun n : ℕ => arrivalTime n ω) atTop atTop)
    (hmono : Monotone (fun n : ℕ => arrivalTime n ω))
    (t : ℝ) (n : ℕ) :
    n < canonicalRenewalCount t ω ↔ arrivalTime n ω ≤ t :=
  lt_canonicalRenewalCount_iff_arrivalTime_le t ω
    (exists_arrivalTime_gt_of_tendsto_atTop ω hω t) hmono n

/-- Equivalent threshold form: the `(n+1)`st count level is reached exactly
when the `n`th finite arrival epoch has occurred. -/
theorem canonicalRenewalCount_succ_le_iff_arrivalTime_le_of_tendsto
    (ω : ℕ → ℝ)
    (hω : Tendsto (fun n : ℕ => arrivalTime n ω) atTop atTop)
    (hmono : Monotone (fun n : ℕ => arrivalTime n ω))
    (t : ℝ) (n : ℕ) :
    n + 1 ≤ canonicalRenewalCount t ω ↔ arrivalTime n ω ≤ t := by
  simpa only [Nat.succ_le_iff] using
    (lt_canonicalRenewalCount_iff_arrivalTime_le_of_tendsto ω hω hmono t n)

/-- A divergent monotone renewal path has a nondecreasing count process. -/
theorem canonicalRenewalCount_monotone_of_tendsto
    (ω : ℕ → ℝ)
    (hω : Tendsto (fun n : ℕ => arrivalTime n ω) atTop atTop) :
    Monotone (fun t : ℝ => canonicalRenewalCount t ω) := by
  intro t u htu
  by_contra hnot
  have hcount_lt : canonicalRenewalCount u ω < canonicalRenewalCount t ω :=
    Nat.lt_of_not_ge hnot
  have htime_le : arrivalTime (canonicalRenewalCount u ω) ω ≤ t :=
    arrivalTime_le_of_lt_canonicalRenewalCount t ω
      (exists_arrivalTime_gt_of_tendsto_atTop ω hω t) hcount_lt
  exact (not_lt_of_ge (htime_le.trans htu))
    (lt_arrivalTime_canonicalRenewalCount u ω
      (exists_arrivalTime_gt_of_tendsto_atTop ω hω u))

/-- At positive rate, the canonical exponential path satisfies the renewal
count threshold identity simultaneously for every finite time and index. -/
theorem ae_lt_canonicalRenewalCount_iff_arrivalTime_le
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      ∀ t : ℝ, ∀ n : ℕ,
        n < canonicalRenewalCount t ω ↔ arrivalTime n ω ≤ t := by
  filter_upwards [ae_arrivalTime_tendsto_atTop hrate,
    ae_arrivalTime_monotone hrate] with ω hdiv hmono
  intro t n
  exact lt_canonicalRenewalCount_iff_arrivalTime_le_of_tendsto ω hdiv hmono t n

/-- At positive rate, the canonical count is almost surely the finite
cardinality of completed renewal epochs, at every finite time. -/
theorem ae_canonicalRenewalCount_eq_ncard_completed
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      ∀ t : ℝ,
        canonicalRenewalCount t ω =
          ({n : ℕ | arrivalTime n ω ≤ t} : Set ℕ).ncard := by
  filter_upwards [ae_arrivalTime_tendsto_atTop hrate,
    ae_arrivalTime_monotone hrate] with ω hdiv hmono
  intro t
  exact canonicalRenewalCount_eq_ncard_completed t ω
    (exists_arrivalTime_gt_of_tendsto_atTop ω hdiv t) hmono

/-- Almost surely, the canonical renewal count is nondecreasing in time. -/
theorem ae_canonicalRenewalCount_monotone
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      Monotone (fun t : ℝ => canonicalRenewalCount t ω) := by
  filter_upwards [ae_arrivalTime_tendsto_atTop hrate] with ω hdiv
  exact canonicalRenewalCount_monotone_of_tendsto ω hdiv

/-- The zero-count fiber consists of paths whose first arrival is after `t`,
together with the (noncanonical) paths that never have a later epoch. -/
theorem canonicalRenewalCount_eq_zero_iff
    (t : ℝ) (ω : ℕ → ℝ) :
    canonicalRenewalCount t ω = 0 ↔
      t < arrivalTime 0 ω ∨ ¬ ∃ n : ℕ, t < arrivalTime n ω := by
  classical
  by_cases h : ∃ n : ℕ, t < arrivalTime n ω
  · rw [canonicalRenewalCount_eq_find t ω h, Nat.find_eq_zero h]
    simp [h]
  · simp [canonicalRenewalCount, h]

/-- A positive count fiber is the finite Boolean combination saying that this
is the first arrival epoch strictly after `t`. -/
theorem canonicalRenewalCount_eq_succ_iff
    (t : ℝ) (ω : ℕ → ℝ) (n : ℕ) :
    canonicalRenewalCount t ω = n + 1 ↔
      t < arrivalTime (n + 1) ω ∧
        ∀ m < n + 1, ¬ t < arrivalTime m ω := by
  classical
  by_cases h : ∃ m : ℕ, t < arrivalTime m ω
  · rw [canonicalRenewalCount_eq_find t ω h, Nat.find_eq_iff h]
  · constructor
    · simp [canonicalRenewalCount, h]
    · intro hpos
      exact (h ⟨n + 1, hpos.1⟩).elim

/-- The canonical renewal count is Borel measurable, including its explicit
fallback value on paths with no epoch after `t`. -/
theorem measurable_canonicalRenewalCount (t : ℝ) :
    Measurable (canonicalRenewalCount t) := by
  classical
  have htime : ∀ n : ℕ,
      MeasurableSet {ω : ℕ → ℝ | t < arrivalTime n ω} := fun n =>
    measurableSet_lt measurable_const (measurable_arrivalTime n)
  have hfuture : MeasurableSet
      {ω : ℕ → ℝ | ∃ n : ℕ, t < arrivalTime n ω} := by
    simpa only [Set.setOf_exists] using
      (MeasurableSet.iUnion htime :
        MeasurableSet (⋃ n : ℕ, {ω : ℕ → ℝ | t < arrivalTime n ω}))
  refine measurable_to_countable' ?_
  intro n
  cases n with
  | zero =>
      have hpreimage : canonicalRenewalCount t ⁻¹' ({0} : Set ℕ) =
          {ω : ℕ → ℝ | t < arrivalTime 0 ω} ∪
            {ω : ℕ → ℝ | ¬ ∃ n : ℕ, t < arrivalTime n ω} := by
        ext ω
        simpa only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union,
          Set.mem_setOf_eq] using (canonicalRenewalCount_eq_zero_iff t ω)
      rw [hpreimage]
      exact (htime 0).union hfuture.compl
  | succ n =>
      have hpreimage : canonicalRenewalCount t ⁻¹' ({n + 1} : Set ℕ) =
          {ω : ℕ → ℝ | t < arrivalTime (n + 1) ω ∧
            ∀ m < n + 1, ¬ t < arrivalTime m ω} := by
        ext ω
        simpa only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq] using
          (canonicalRenewalCount_eq_succ_iff t ω n)
      rw [hpreimage]
      simp only [Set.setOf_and, Set.setOf_forall, ← Set.compl_setOf]
      repeat' apply_rules [MeasurableSet.inter, MeasurableSet.iInter,
        MeasurableSet.compl, htime] <;> try intros

/-- Joint measurability of the canonical renewal count in its clock time and
interarrival path.  This is needed when a later construction randomizes a
deterministic clock value; it does not itself give an increment law at that
random clock. -/
theorem measurable_canonicalRenewalCount_joint :
    Measurable (fun p : ℝ × (ℕ → ℝ) => canonicalRenewalCount p.1 p.2) := by
  classical
  have htime : ∀ n : ℕ,
      MeasurableSet {p : ℝ × (ℕ → ℝ) | p.1 < arrivalTime n p.2} := fun n =>
    measurableSet_lt measurable_fst ((measurable_arrivalTime n).comp measurable_snd)
  have hfuture : MeasurableSet
      {p : ℝ × (ℕ → ℝ) | ∃ n : ℕ, p.1 < arrivalTime n p.2} := by
    simpa only [Set.setOf_exists] using
      (MeasurableSet.iUnion htime :
        MeasurableSet (⋃ n : ℕ, {p : ℝ × (ℕ → ℝ) | p.1 < arrivalTime n p.2}))
  refine measurable_to_countable' ?_
  intro n
  cases n with
  | zero =>
      have hpreimage :
          (fun p : ℝ × (ℕ → ℝ) => canonicalRenewalCount p.1 p.2) ⁻¹'
            ({0} : Set ℕ) =
          {p : ℝ × (ℕ → ℝ) | p.1 < arrivalTime 0 p.2} ∪
            {p : ℝ × (ℕ → ℝ) | ¬ ∃ n : ℕ, p.1 < arrivalTime n p.2} := by
        ext p
        simpa only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union,
          Set.mem_setOf_eq] using (canonicalRenewalCount_eq_zero_iff p.1 p.2)
      rw [hpreimage]
      exact (htime 0).union hfuture.compl
  | succ n =>
      have hpreimage :
          (fun p : ℝ × (ℕ → ℝ) => canonicalRenewalCount p.1 p.2) ⁻¹'
            ({n + 1} : Set ℕ) =
          {p : ℝ × (ℕ → ℝ) | p.1 < arrivalTime (n + 1) p.2 ∧
            ∀ m < n + 1, ¬ p.1 < arrivalTime m p.2} := by
        ext p
        simpa only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq] using
          (canonicalRenewalCount_eq_succ_iff p.1 p.2 n)
      rw [hpreimage]
      simp only [Set.setOf_and, Set.setOf_forall, ← Set.compl_setOf]
      repeat' apply_rules [MeasurableSet.inter, MeasurableSet.iInter,
        MeasurableSet.compl, htime] <;> try intros

/-- Natural continuous-time filtration of the canonical renewal-count process. -/
noncomputable def canonicalRenewalCountFiltration :
    Filtration (Ω := ℕ → ℝ) ℝ inferInstance :=
  Filtration.natural canonicalRenewalCount
    (fun t => (measurable_canonicalRenewalCount t).stronglyMeasurable)

/-- The canonical renewal count is adapted to its natural filtration. -/
theorem canonicalRenewalCount_adapted :
    Adapted canonicalRenewalCountFiltration canonicalRenewalCount := by
  unfold canonicalRenewalCountFiltration
  exact (Filtration.stronglyAdapted_natural
    (fun t => (measurable_canonicalRenewalCount t).stronglyMeasurable)).adapted

end
end PoissonProcess
end Probability
end EconCSLib
