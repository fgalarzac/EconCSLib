import EconCSLib.Foundations.Probability.PoissonSuspensionStationaryBase
import EconCSLib.Foundations.Probability.PalmCampbell

/-!
# Stationary arrivals carried by the Poisson suspension

This module equips the literal good-state Poisson suspension with its
untagged ordered arrival process, exact finite window enumerators, and the
recentring map to the iid Palm-gap path. It proves every structural field of
the Campbell/Palm certificate. The remaining field is deliberately an
explicit marked unit-window mass-transport equality.
-/

namespace EconCSLib.Probability.PoissonProcess

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- The untagged arrival epochs in the stationary suspension state. -/
def suspensionBaseArrival (p : GoodSuspensionState) (i : ℤ) : ℝ :=
  candidatePalmArrival p.1.1 i - p.1.2

theorem measurable_suspensionBaseArrival (i : ℤ) :
    Measurable (fun p : GoodSuspensionState => suspensionBaseArrival p i) := by
  exact ((measurable_candidatePalmArrival i).comp
    (measurable_fst.comp measurable_subtype_coe)).sub
      (measurable_snd.comp measurable_subtype_coe)

theorem suspensionBaseArrival_strictMono (p : GoodSuspensionState) :
    StrictMono (suspensionBaseArrival p) := by
  intro i j hij
  exact sub_lt_sub_right
    (suspensionGoodGapPath_strictMono p.1.1 p.2.2 hij) _

/-- The iid-gap candidate path obtained by choosing base arrival `i` as tag. -/
def suspensionBaseRecenter (p : GoodSuspensionState) (i : ℤ) : ℤ → ℝ :=
  suspensionGapShift i p.1.1

theorem measurable_suspensionBaseRecenter (i : ℤ) :
    Measurable (fun p : GoodSuspensionState => suspensionBaseRecenter p i) := by
  exact (measurable_suspensionGapShift i).comp
    (measurable_fst.comp measurable_subtype_coe)

theorem suspensionBaseRecenter_arrivals
    (p : GoodSuspensionState) (i j : ℤ) :
    candidatePalmArrival (suspensionBaseRecenter p i) j =
      suspensionBaseArrival p (i + j) - suspensionBaseArrival p i := by
  change candidatePalmArrival (suspensionGapShift i p.1.1) j =
    suspensionBaseArrival p (i + j) - suspensionBaseArrival p i
  rw [candidatePalmArrival_suspensionGapShift]
  simp only [suspensionBaseArrival]
  ring

/-- The recenter map has the candidate iid Palm-gap path as its tagged target
type; the displayed equality is the corresponding arrival-path field. Its law
under a *selected* base arrival is the remaining Campbell identity. -/
theorem suspensionBaseRecenter_candidateTagged_arrivals
    {rate : ℝ} (hrate : 0 < rate) (p : GoodSuspensionState) (i j : ℤ) :
    (candidateTaggedArrivalAtZero rate hrate).arrivals
        (suspensionBaseRecenter p i) j =
      suspensionBaseArrival p (i + j) - suspensionBaseArrival p i := by
  exact suspensionBaseRecenter_arrivals p i j

/-- A finite candidate set containing exactly all indices with stationary-base
arrival epoch in `[a,b)`. Filtering makes the endpoint convention literal;
the two crossing labels make the containing interval finite. -/
def suspensionBaseArrivalIndices (a b : ℝ) (p : GoodSuspensionState) : Finset ℤ :=
  (Finset.Icc (suspensionCrossingIndexPastClosed a p.1)
    (suspensionCrossingIndexPastClosed b p.1)).filter
      (fun i => a ≤ suspensionBaseArrival p i ∧ suspensionBaseArrival p i < b)

theorem suspensionBaseArrival_crossing_interval
    (p : GoodSuspensionState) (t : ℝ) :
    let k := suspensionCrossingIndexPastClosed t p.1
    suspensionBaseArrival p k ≤ t ∧ t < suspensionBaseArrival p (k + 1) := by
  dsimp
  have h := suspensionCrossingIndexPastClosed_interval p.1.1
    (suspensionGoodGapPath_future p.1.1 p.2.2)
    (suspensionGoodGapPath_past p.1.1 p.2.2) p.1.2 t
  dsimp at h
  change candidatePalmArrival p.1.1 (suspensionCrossingIndexPastClosed t p.1) - p.1.2 ≤ t ∧
    t < candidatePalmArrival p.1.1 (suspensionCrossingIndexPastClosed t p.1 + 1) - p.1.2
  constructor <;> linarith [h.1, h.2]

theorem mem_suspensionBaseArrivalIndices_iff
    (a b : ℝ) (p : GoodSuspensionState) (i : ℤ) :
    i ∈ suspensionBaseArrivalIndices a b p ↔
      a ≤ suspensionBaseArrival p i ∧ suspensionBaseArrival p i < b := by
  constructor
  · intro hi
    exact (Finset.mem_filter.mp hi).2
  · intro hi
    have ha := suspensionBaseArrival_crossing_interval p a
    have hb := suspensionBaseArrival_crossing_interval p b
    have hlow : suspensionCrossingIndexPastClosed a p.1 ≤ i := by
      by_contra hnot
      have hiless : i < suspensionCrossingIndexPastClosed a p.1 := lt_of_not_ge hnot
      have harrival := suspensionBaseArrival_strictMono p hiless
      linarith [ha.1]
    have hupp : i ≤ suspensionCrossingIndexPastClosed b p.1 := by
      by_contra hnot
      have hiless : suspensionCrossingIndexPastClosed b p.1 < i := lt_of_not_ge hnot
      have hnext : suspensionCrossingIndexPastClosed b p.1 + 1 ≤ i := by omega
      have harrival := (suspensionBaseArrival_strictMono p).monotone hnext
      linarith [hb.2]
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlow, hupp⟩, hi⟩

theorem suspensionBaseArrival_goodSuspensionFlow
    (p : GoodSuspensionState) (t : ℝ) (j : ℤ) :
    suspensionBaseArrival (goodSuspensionFlow t p) j =
      suspensionBaseArrival p
        (suspensionCrossingIndexPastClosed t p.1 + j) - t := by
  change candidatePalmArrival (suspensionFlow t p.1).1 j -
      (suspensionFlow t p.1).2 =
    suspensionBaseArrival p
      (suspensionCrossingIndexPastClosed t p.1 + j) - t
  simp only [suspensionFlow]
  rw [candidatePalmArrival_suspensionGapShift]
  simp only [suspensionBaseArrival]
  ring

theorem suspensionBaseArrival_range_goodSuspensionFlow
    (p : GoodSuspensionState) (t : ℝ) :
    Set.range (suspensionBaseArrival (goodSuspensionFlow t p)) =
      (fun u : ℝ => u - t) '' Set.range (suspensionBaseArrival p) := by
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨suspensionBaseArrival p
      (suspensionCrossingIndexPastClosed t p.1 + j), ⟨_, rfl⟩, ?_⟩
    exact (suspensionBaseArrival_goodSuspensionFlow p t j).symm
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    let k := suspensionCrossingIndexPastClosed t p.1
    refine ⟨i - k, ?_⟩
    rw [suspensionBaseArrival_goodSuspensionFlow]
    have hindex : k + (i - k) = i := by dsimp [k]; omega
    rw [hindex]

/-- The finite marked unit-window count is measurable for every measurable
candidate-tagged event. This closes the measurability field of the eventual
Campbell certificate independently of its still-open mass-transport identity. -/
theorem measurable_suspensionBaseMarkedUnitWindowCount
    (s : Set (ℤ → ℝ)) (hs : MeasurableSet s) :
    Measurable (fun p : GoodSuspensionState =>
      Palm.unitWindowCampbellCount suspensionBaseArrivalIndices
        suspensionBaseRecenter s p) := by
  classical
  let state : GoodSuspensionState → ℤ × ℤ := fun p =>
    (suspensionCrossingIndexPastClosed 0 p.1,
      suspensionCrossingIndexPastClosed 1 p.1)
  let indices : ℤ × ℤ → Finset ℤ := fun n => Finset.Icc n.1 n.2
  have hstate : Measurable state := by
    exact ((measurable_suspensionCrossingIndexPastClosed 0).comp measurable_subtype_coe).prodMk
      ((measurable_suspensionCrossingIndexPastClosed 1).comp measurable_subtype_coe)
  let selected : GoodSuspensionState → ℤ → Bool := fun p i =>
    decide (0 ≤ suspensionBaseArrival p i ∧ suspensionBaseArrival p i < 1 ∧
      suspensionBaseRecenter p i ∈ s)
  have hselected : Measurable selected := by
    refine measurable_pi_iff.2 fun i => ?_
    change Measurable (fun p => if
      0 ≤ suspensionBaseArrival p i ∧ suspensionBaseArrival p i < 1 ∧
        suspensionBaseRecenter p i ∈ s then true else false)
    have hleft : MeasurableSet {p : GoodSuspensionState |
        (0 : ℝ) ≤ suspensionBaseArrival p i} :=
      measurableSet_le measurable_const (measurable_suspensionBaseArrival i)
    have hright : MeasurableSet {p : GoodSuspensionState |
        suspensionBaseArrival p i < (1 : ℝ)} :=
      measurableSet_lt (measurable_suspensionBaseArrival i) measurable_const
    have hmark : MeasurableSet {p : GoodSuspensionState |
        suspensionBaseRecenter p i ∈ s} :=
      (measurable_suspensionBaseRecenter i) hs
    exact Measurable.ite (hleft.inter (hright.inter hmark))
      measurable_const measurable_const
  have hcount := Palm.measurable_count_from_countable_parameter state hstate indices
    selected hselected
  change Measurable (fun p =>
    ((suspensionBaseArrivalIndices 0 1 p).filter fun i =>
      suspensionBaseRecenter p i ∈ s).card)
  convert hcount using 1
  funext p
  simp only [state, indices, selected, suspensionBaseArrivalIndices,
    Finset.filter_filter, decide_eq_true_eq]
  congr 1
  apply Finset.filter_congr
  intro i hi
  constructor <;> intro h
  · exact ⟨h.1.1, h.1.2, h.2⟩
  · exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

/-- The raw fixed-index summand in the marked suspension transport.  It is
the same selected-arrival event as the good-state Campbell count, before the
full-measure good carrier is packaged as a subtype. -/
noncomputable def suspensionMarkedUnitSummand
    (s : Set (ℤ → ℝ)) (i : ℤ) (p : (ℤ → ℝ) × ℝ) : ℝ≥0∞ := by
  classical
  exact if 0 ≤ candidatePalmArrival p.1 i - p.2 ∧
      candidatePalmArrival p.1 i - p.2 < 1 ∧
      suspensionGapShift i p.1 ∈ s then 1 else 0

theorem measurable_suspensionMarkedUnitSummand
    (s : Set (ℤ → ℝ)) (hs : MeasurableSet s) (i : ℤ) :
    Measurable (suspensionMarkedUnitSummand s i) := by
  classical
  have hleft : MeasurableSet {p : (ℤ → ℝ) × ℝ |
      (0 : ℝ) ≤ candidatePalmArrival p.1 i - p.2} :=
    measurableSet_le measurable_const
      (((measurable_candidatePalmArrival i).comp measurable_fst).sub measurable_snd)
  have hright : MeasurableSet {p : (ℤ → ℝ) × ℝ |
      candidatePalmArrival p.1 i - p.2 < (1 : ℝ)} :=
    measurableSet_lt
      (((measurable_candidatePalmArrival i).comp measurable_fst).sub measurable_snd)
      measurable_const
  have hmark : MeasurableSet {p : (ℤ → ℝ) × ℝ |
      suspensionGapShift i p.1 ∈ s} :=
    ((measurable_suspensionGapShift i).comp measurable_fst) hs
  change Measurable (fun p : (ℤ → ℝ) × ℝ => if
      0 ≤ candidatePalmArrival p.1 i - p.2 ∧
        candidatePalmArrival p.1 i - p.2 < 1 ∧
        suspensionGapShift i p.1 ∈ s then (1 : ℝ≥0∞) else 0)
  exact Measurable.ite (hleft.inter (hright.inter hmark))
    measurable_const measurable_const

/-- The remaining raw mass-transport theorem: fixed-index reindexing carries
the selected branches to a partition of a unit phase strip. -/
def HasSuspensionMarkedUnitTransport (rate : ℝ) : Prop :=
  ∀ s : Set (ℤ → ℝ), MeasurableSet s →
    ∑' i : ℤ, ∫⁻ p, suspensionMarkedUnitSummand s i p
      ∂suspensionMeasure rate =
      ENNReal.ofReal rate * twoSidedInterarrivalMeasure rate s

/-- On the literal good suspension state space, the finite marked unit-window
count is the finite sum of the raw fixed-index summands. -/
theorem suspensionBaseMarkedUnitWindowCount_eq_sum
    (s : Set (ℤ → ℝ)) (p : GoodSuspensionState) :
    Palm.unitWindowCampbellCount
      suspensionBaseArrivalIndices suspensionBaseRecenter s p =
      (by
        classical
        exact ∑ i ∈ suspensionBaseArrivalIndices 0 1 p,
          if 0 ≤ suspensionBaseArrival p i ∧
              suspensionBaseArrival p i < 1 ∧
              suspensionBaseRecenter p i ∈ s then 1 else 0) := by
  classical
  change ((suspensionBaseArrivalIndices 0 1 p).filter fun i =>
    suspensionBaseRecenter p i ∈ s).card = _
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i hi
  have hinterval : 0 ≤ suspensionBaseArrival p i ∧
      suspensionBaseArrival p i < 1 :=
    (mem_suspensionBaseArrivalIndices_iff 0 1 p i).mp hi
  by_cases hmark : suspensionBaseRecenter p i ∈ s
  · simp [hinterval, hmark]
  · simp [hinterval, hmark]

theorem suspensionBaseMarkedUnitWindowCount_coe_eq_tsum
    (s : Set (ℤ → ℝ)) (p : GoodSuspensionState) :
    (Palm.unitWindowCampbellCount
      suspensionBaseArrivalIndices suspensionBaseRecenter s p : ℝ≥0∞) =
      ∑' i : ℤ, suspensionMarkedUnitSummand s i p.1 := by
  classical
  rw [suspensionBaseMarkedUnitWindowCount_eq_sum]
  rw [tsum_eq_sum (s := suspensionBaseArrivalIndices 0 1 p)]
  · simp only [suspensionMarkedUnitSummand]
    norm_cast
  · intro i hi
    have hnot : ¬ (0 ≤ suspensionBaseArrival p i ∧
        suspensionBaseArrival p i < 1) := by
      intro h
      exact hi ((mem_suspensionBaseArrivalIndices_iff 0 1 p i).mpr h)
    change suspensionMarkedUnitSummand s i p.1 = 0
    change (if 0 ≤ suspensionBaseArrival p i ∧
        suspensionBaseArrival p i < 1 ∧
        suspensionBaseRecenter p i ∈ s then (1 : ℝ≥0∞) else 0) = 0
    have hnot' : ¬ (0 ≤ suspensionBaseArrival p i ∧
        suspensionBaseArrival p i < 1 ∧ suspensionBaseRecenter p i ∈ s) := by
      rintro ⟨hzero, hone, _⟩
      exact hnot ⟨hzero, hone⟩
    simp [hnot']

/-- Coercing the good carrier back to the raw suspension coordinates pushes
its probability law exactly to the normalized suspension measure. -/
theorem map_goodSuspensionMeasure_subtype_val
    {rate : ℝ} (hrate : 0 < rate) :
    Measure.map (Subtype.val : GoodSuspensionState → ((ℤ → ℝ) × ℝ))
      (goodSuspensionMeasure rate) = suspensionMeasure rate := by
  let I : GoodSuspensionState → ((ℤ → ℝ) × ℝ) := Subtype.val
  have hI : MeasurableEmbedding I :=
    MeasurableEmbedding.subtype_coe measurableSet_goodSuspensionState
  change Measure.map I (Measure.comap I (suspensionMeasure rate)) =
    suspensionMeasure rate
  rw [hI.map_comap]
  apply Measure.restrict_eq_self_of_ae_mem
  filter_upwards [ae_goodSuspensionState hrate] with p hp
  exact ⟨⟨p, hp⟩, rfl⟩

/-- A raw marked branch-transport theorem yields the exact marked
unit-window formula for the stationary good-suspension base.  This removes
all subtype and Tonelli bookkeeping from the remaining analytic seam. -/
theorem suspensionBaseMarkedUnitCampbell_of_transport
    {rate : ℝ} (hrate : 0 < rate)
    (htransport : HasSuspensionMarkedUnitTransport rate)
    (s : Set (ℤ → ℝ)) (hs : MeasurableSet s) :
    ∫⁻ p, (Palm.unitWindowCampbellCount
      suspensionBaseArrivalIndices suspensionBaseRecenter s p : ℝ≥0∞)
      ∂goodSuspensionMeasure rate =
      ENNReal.ofReal rate * twoSidedInterarrivalMeasure rate s := by
  calc
    ∫⁻ p, (Palm.unitWindowCampbellCount
        suspensionBaseArrivalIndices suspensionBaseRecenter s p : ℝ≥0∞)
        ∂goodSuspensionMeasure rate =
      ∫⁻ p, ∑' i : ℤ, suspensionMarkedUnitSummand s i p.1
        ∂goodSuspensionMeasure rate := by
          apply MeasureTheory.lintegral_congr
          intro p
          exact suspensionBaseMarkedUnitWindowCount_coe_eq_tsum s p
    _ = ∑' i : ℤ, ∫⁻ p, suspensionMarkedUnitSummand s i p.1
        ∂goodSuspensionMeasure rate := by
          exact MeasureTheory.lintegral_tsum fun i =>
            ((measurable_suspensionMarkedUnitSummand s hs i).comp
              measurable_subtype_coe).aemeasurable
    _ = ∑' i : ℤ, ∫⁻ p, suspensionMarkedUnitSummand s i p
        ∂suspensionMeasure rate := by
          apply tsum_congr
          intro i
          calc
            ∫⁻ p, suspensionMarkedUnitSummand s i p.1
                ∂goodSuspensionMeasure rate =
                ∫⁻ p, suspensionMarkedUnitSummand s i p
                  ∂Measure.map (Subtype.val : GoodSuspensionState → ((ℤ → ℝ) × ℝ))
                    (goodSuspensionMeasure rate) := by
                      exact (MeasureTheory.lintegral_map
                        (measurable_suspensionMarkedUnitSummand s hs i)
                        measurable_subtype_coe).symm
            _ = ∫⁻ p, suspensionMarkedUnitSummand s i p
                ∂suspensionMeasure rate := by
                  rw [map_goodSuspensionMeasure_subtype_val hrate]
    _ = ENNReal.ofReal rate * twoSidedInterarrivalMeasure rate s :=
      htransport s hs

/-- Certificate-ready pointwise facts, expressed in the almost-everywhere
form used by `CampbellPalmTaggedArrivalCertificate`. -/
theorem ae_suspensionBaseArrival_strict
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ p ∂(goodSuspensionShiftInvariantLaw hrate).Pbase,
      StrictMono (suspensionBaseArrival p) :=
  Filter.Eventually.of_forall suspensionBaseArrival_strictMono

theorem ae_suspensionBaseArrivalIndices_spec
    {rate : ℝ} (hrate : 0 < rate) (a b : ℝ) :
    ∀ᵐ p ∂(goodSuspensionShiftInvariantLaw hrate).Pbase, ∀ i,
      i ∈ suspensionBaseArrivalIndices a b p ↔
        a ≤ suspensionBaseArrival p i ∧ suspensionBaseArrival p i < b :=
  Filter.Eventually.of_forall fun p i =>
    mem_suspensionBaseArrivalIndices_iff a b p i

theorem ae_suspensionBaseArrival_shift
    {rate : ℝ} (hrate : 0 < rate) (t : ℝ) :
    ∀ᵐ p ∂(goodSuspensionShiftInvariantLaw hrate).Pbase,
      Set.range (suspensionBaseArrival
        ((goodSuspensionShiftInvariantLaw hrate).shift t p)) =
        (fun u : ℝ => u - t) '' Set.range (suspensionBaseArrival p) :=
  Filter.Eventually.of_forall fun p =>
    suspensionBaseArrival_range_goodSuspensionFlow p t

/-- All non-mass-transport fields of the stationary Campbell/Palm certificate
are now concrete. Supplying `hcampbell` is exactly the remaining marked
Campbell theorem; it is not hidden by this constructor. -/
noncomputable def goodSuspensionCampbellCertificate
    {rate : ℝ} (hrate : 0 < rate)
    (hcampbell : ∀ s : Set (ℤ → ℝ), MeasurableSet s →
      ∫⁻ p, (↑(Palm.unitWindowCampbellCount suspensionBaseArrivalIndices
        suspensionBaseRecenter s p) : ENNReal)
        ∂(goodSuspensionShiftInvariantLaw hrate).Pbase =
        ENNReal.ofReal rate * (candidateTaggedArrivalAtZero rate hrate).Ptag s) :
    Palm.CampbellPalmTaggedArrivalCertificate
      (goodSuspensionShiftInvariantLaw hrate)
      (candidateTaggedArrivalAtZero rate hrate) where
  arrivalRate := rate
  arrivalRate_pos := hrate
  baseArrivals := suspensionBaseArrival
  baseArrivals_measurable := measurable_suspensionBaseArrival
  baseArrivals_strict := ae_suspensionBaseArrival_strict hrate
  arrivalsIn := suspensionBaseArrivalIndices
  arrivalsIn_spec := fun a b => ae_suspensionBaseArrivalIndices_spec hrate a b
  recenterAt := suspensionBaseRecenter
  recenterAt_measurable := measurable_suspensionBaseRecenter
  recenter_arrivals := Filter.Eventually.of_forall fun p i j =>
    suspensionBaseRecenter_candidateTagged_arrivals hrate p i j
  baseArrivals_shift := fun t => ae_suspensionBaseArrival_shift hrate t
  campbellCount_aemeasurable := fun s hs =>
    (measurable_suspensionBaseMarkedUnitWindowCount s hs).aemeasurable
  campbell_unit_interval := hcampbell

/-- The raw fixed-index transport closes the sole analytic field of the
good-suspension Campbell/Palm certificate. -/
noncomputable def goodSuspensionCampbellCertificate_of_transport
    {rate : ℝ} (hrate : 0 < rate)
    (htransport : HasSuspensionMarkedUnitTransport rate) :
    Palm.CampbellPalmTaggedArrivalCertificate
      (goodSuspensionShiftInvariantLaw hrate)
      (candidateTaggedArrivalAtZero rate hrate) :=
  goodSuspensionCampbellCertificate hrate (fun s hs => by
    simpa [candidateTaggedArrivalAtZero] using
      (suspensionBaseMarkedUnitCampbell_of_transport hrate htransport s hs))

end

end EconCSLib.Probability.PoissonProcess
