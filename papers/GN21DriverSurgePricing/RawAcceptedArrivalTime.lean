import GN21DriverSurgePricing.AcceptedTripSelection

/-!
# Literal first accepted-arrival time for GN21

This module keeps the marked-Poisson timing construction on the original raw
GN21 clock-and-mark product seed.  In particular, the first accepted-arrival
time is an observable of that seed, rather than a coordinate of a separately
supplied post-thinning model.
-/

namespace GN21DriverSurgePricing

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

namespace AcceptedArrivalTime

/-- The literal raw trip-mark stream selected by a source state. -/
def rawTripMarkStream (state : Fin 2) : GN21RawCycleSeed -> Nat -> TripLength :=
  fun seed n => gn21RawCycleMark state n seed

/-- The literal raw exponential interarrival stream selected by a source
clock. -/
def rawClockStream (clock : Fin 4) : GN21RawCycleSeed -> Nat -> Real :=
  fun seed n => gn21RawCycleClock clock n seed

/-- The actual arrival time of the first raw request whose trip mark is
accepted.  It is totalized only on the null no-accepted-mark event through
`firstAcceptedIndex`. -/
noncomputable def gn21RawFirstAcceptedArrivalTime
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy) :
    GN21RawCycleSeed -> Real :=
  fun seed => EconCSLib.Probability.PoissonProcess.arrivalTime
    (AcceptedTripSelection.firstAcceptedIndex sigma (rawTripMarkStream state seed))
    (rawClockStream clock seed)

theorem measurable_rawTripMarkStream (state : Fin 2) :
    Measurable (rawTripMarkStream state) := by
  apply measurable_pi_lambda
  intro n
  exact ((measurable_pi_apply n).comp
    ((measurable_pi_apply state).comp measurable_snd))

theorem measurable_rawClockStream (clock : Fin 4) :
    Measurable (rawClockStream clock) := by
  apply measurable_pi_lambda
  intro n
  exact ((measurable_pi_apply n).comp
    ((measurable_pi_apply clock).comp measurable_fst))

theorem measurable_rawFirstAcceptedIndex
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (fun seed : GN21RawCycleSeed =>
      AcceptedTripSelection.firstAcceptedIndex sigma (rawTripMarkStream state seed)) := by
  exact (AcceptedTripSelection.measurable_firstAcceptedIndex sigma hsigma).comp
    (measurable_rawTripMarkStream state)

theorem measurable_gn21RawFirstAcceptedArrivalTime
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma) :
    Measurable (gn21RawFirstAcceptedArrivalTime clock state sigma) := by
  let index : GN21RawCycleSeed -> Nat := fun seed =>
    AcceptedTripSelection.firstAcceptedIndex sigma (rawTripMarkStream state seed)
  have hindex : Measurable index := by
    simpa [index] using measurable_rawFirstAcceptedIndex state sigma hsigma
  have hindex_event : forall n, MeasurableSet {seed | index seed = n} := by
    intro n
    simpa only [Set.preimage_setOf_eq] using hindex (measurableSet_singleton n)
  let h : forall seed : GN21RawCycleSeed, exists n, index seed = n :=
    fun seed => ⟨index seed, rfl⟩
  have hmeas : Measurable (fun seed : GN21RawCycleSeed =>
      EconCSLib.Probability.PoissonProcess.arrivalTime (Nat.find (h seed))
        (rawClockStream clock seed)) :=
    Measurable.find
      (fun n =>
        (EconCSLib.Probability.PoissonProcess.measurable_arrivalTime n).comp
          (measurable_rawClockStream clock))
      hindex_event h
  convert hmeas using 1
  funext seed
  have hfind : Nat.find (h seed) = index seed := (Nat.find_spec (h seed)).symm
  simp [gn21RawFirstAcceptedArrivalTime, index, hfind]

/-- At a fixed raw-clock horizon, the accepted-count is zero exactly when
every actual raw request before that horizon is rejected. -/
theorem rawAcceptedRequestCount_eq_zero_iff
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy)
    (t : Real) (seed : GN21RawCycleSeed) :
    gn21RawAcceptedRequestCount clock state sigma t seed = 0 ↔
      ∀ i : Fin (EconCSLib.Probability.PoissonProcess.canonicalRenewalCount t
        (seed.1 clock)), rawTripMarkStream state seed i ∉ sigma := by
  classical
  unfold gn21RawAcceptedRequestCount gn21RawFiniteHorizonMarkedSample
  unfold EconCSLib.Probability.FiniteHorizonMarkedPoisson.kept
    EconCSLib.Probability.FiniteHorizonMarkedPoisson.keptInMarks
  rw [Finset.card_eq_zero]
  rw [EconCSLib.successIndexSet_eq_iff]
  simp [rawTripMarkStream, gn21AcceptanceMark]

private theorem rawClockRate_pos
    (arrivalI arrivalJ switchIJ switchJI : Real)
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) :
    0 < gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock := by
  fin_cases clock <;>
    simp [gn21CycleClockRate, harrivalI, harrivalJ, hswitchIJ, hswitchJI]

private theorem measurableSet_exists_accepted
    (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    MeasurableSet {marks : Nat -> TripLength | ∃ n, marks n ∈ sigma} := by
  rw [show {marks : Nat -> TripLength | ∃ n, marks n ∈ sigma} =
      ⋃ n, {marks | marks n ∈ sigma} by
        ext marks
        simp]
  apply MeasurableSet.iUnion
  intro n
  exact (measurable_pi_apply n) hsigma

/-- Positive accepted source mass makes the literal raw GN21 mark stream
contain an accepted trip almost surely. -/
theorem ae_rawTripMarkStream_exists_accepted
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    ∀ᵐ seed ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI,
      ∃ n, rawTripMarkStream state seed n ∈ sigma := by
  let M := gn21CycleMarkLaw muI muJ state
  have hM_prob : IsProbabilityMeasure M := by
    dsimp [M, gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure M := hM_prob
  have hsource : ∀ᵐ marks ∂IIDStream.measure M, ∃ n, marks n ∈ sigma :=
    AcceptedTripSelection.ae_exists_accepted M sigma hsigma (by simpa [M] using hmass)
  have hraw := gn21RawCycleMarkStream_hasLaw muI muJ arrivalI arrivalJ
    switchIJ switchJI harrivalI harrivalJ hswitchIJ hswitchJI state
  have hsource_map : ∀ᵐ marks ∂Measure.map (rawTripMarkStream state)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI),
      ∃ n, marks n ∈ sigma := by
    change ∀ᵐ marks ∂Measure.map (fun seed : GN21RawCycleSeed => seed.2 state)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI),
      ∃ n, marks n ∈ sigma
    rw [hraw.map_eq]
    simpa [rawTripMarkStream, M] using hsource
  have hpull := (MeasureTheory.ae_map_iff hraw.aemeasurable
    (measurableSet_exists_accepted sigma hsigma)).mp hsource_map
  simpa [rawTripMarkStream] using hpull

private theorem measurableSet_all_nonnegative_rawClock :
    MeasurableSet {clockPath : Nat -> Real | ∀ n, 0 ≤ clockPath n} := by
  rw [show {clockPath : Nat -> Real | ∀ n, 0 ≤ clockPath n} =
      ⋂ n, {clockPath | 0 ≤ clockPath n} by
        ext clockPath
        simp]
  apply MeasurableSet.iInter
  intro n
  exact (measurable_pi_apply n) measurableSet_Ici

/-- The literal raw GN21 clock path has nonnegative gaps almost surely. -/
theorem ae_rawClockStream_nonnegative
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) :
    ∀ᵐ seed ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI,
      ∀ n, 0 ≤ rawClockStream clock seed n := by
  let rate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock
  have hrate : 0 < rate := rawClockRate_pos arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI clock
  have hsource : ∀ᵐ clockPath
      ∂EconCSLib.Probability.PoissonProcess.exponentialInterarrivalMeasure rate,
      ∀ n, 0 ≤ clockPath n :=
    (EconCSLib.Probability.PoissonProcess.ae_all_interarrival_positive hrate).mono
      (fun _ hpos n => (hpos n).le)
  have hraw := gn21RawCycleClockStream_hasLaw muI muJ arrivalI arrivalJ
    switchIJ switchJI harrivalI harrivalJ hswitchIJ hswitchJI clock
  have hsource_map : ∀ᵐ clockPath ∂Measure.map (rawClockStream clock)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI),
      ∀ n, 0 ≤ clockPath n := by
    change ∀ᵐ clockPath ∂Measure.map (fun seed : GN21RawCycleSeed => seed.1 clock)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI),
      ∀ n, 0 ≤ clockPath n
    rw [hraw.map_eq]
    simpa [rawClockStream, rate] using hsource
  have hpull := (MeasureTheory.ae_map_iff hraw.aemeasurable
    measurableSet_all_nonnegative_rawClock).mp hsource_map
  simpa [rawClockStream] using hpull

private theorem measurableSet_rawClock_count_threshold (t : Real) :
    MeasurableSet {clockPath : Nat -> Real |
      ∀ n, n < EconCSLib.Probability.PoissonProcess.canonicalRenewalCount t clockPath ↔
        EconCSLib.Probability.PoissonProcess.arrivalTime n clockPath ≤ t} := by
  rw [show {clockPath : Nat -> Real |
      ∀ n, n < EconCSLib.Probability.PoissonProcess.canonicalRenewalCount t clockPath ↔
        EconCSLib.Probability.PoissonProcess.arrivalTime n clockPath ≤ t} =
      ⋂ n, {clockPath |
        n < EconCSLib.Probability.PoissonProcess.canonicalRenewalCount t clockPath ↔
          EconCSLib.Probability.PoissonProcess.arrivalTime n clockPath ≤ t} by
        ext clockPath
        simp]
  apply MeasurableSet.iInter
  intro n
  exact
    (measurableSet_lt measurable_const
      (EconCSLib.Probability.PoissonProcess.measurable_canonicalRenewalCount t)).iff
      (measurableSet_le
        (EconCSLib.Probability.PoissonProcess.measurable_arrivalTime n)
        measurable_const)

/-- The raw clock's count/arrival threshold relation holds almost surely at
every request index for a fixed calendar time. -/
theorem ae_rawClock_count_threshold
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) (t : Real) :
    ∀ᵐ seed ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI,
      ∀ n, n < EconCSLib.Probability.PoissonProcess.canonicalRenewalCount t
        (rawClockStream clock seed) ↔
        EconCSLib.Probability.PoissonProcess.arrivalTime n
          (rawClockStream clock seed) ≤ t := by
  let rate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock
  have hrate : 0 < rate := rawClockRate_pos arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI clock
  have hsource : ∀ᵐ clockPath
      ∂EconCSLib.Probability.PoissonProcess.exponentialInterarrivalMeasure rate,
      ∀ n, n < EconCSLib.Probability.PoissonProcess.canonicalRenewalCount t clockPath ↔
        EconCSLib.Probability.PoissonProcess.arrivalTime n clockPath ≤ t :=
    (EconCSLib.Probability.PoissonProcess.ae_lt_canonicalRenewalCount_iff_arrivalTime_le
      hrate).mono (fun _ hthreshold n => hthreshold t n)
  have hraw := gn21RawCycleClockStream_hasLaw muI muJ arrivalI arrivalJ
    switchIJ switchJI harrivalI harrivalJ hswitchIJ hswitchJI clock
  have hsource_map : ∀ᵐ clockPath ∂Measure.map (rawClockStream clock)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI),
      ∀ n, n < EconCSLib.Probability.PoissonProcess.canonicalRenewalCount t clockPath ↔
        EconCSLib.Probability.PoissonProcess.arrivalTime n clockPath ≤ t := by
    change ∀ᵐ clockPath ∂Measure.map (fun seed : GN21RawCycleSeed => seed.1 clock)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI),
      ∀ n, n < EconCSLib.Probability.PoissonProcess.canonicalRenewalCount t clockPath ↔
        EconCSLib.Probability.PoissonProcess.arrivalTime n clockPath ≤ t
    rw [hraw.map_eq]
    simpa [rawClockStream, rate] using hsource
  have hpull := (MeasureTheory.ae_map_iff hraw.aemeasurable
    (measurableSet_rawClock_count_threshold t)).mp hsource_map
  simpa [rawClockStream] using hpull

/-- On a path with an accepted raw mark and a nonexplosive monotone request
clock, the first accepted-arrival time exceeds `t` exactly when the raw
accepted-request count through `t` is zero. -/
theorem rawAcceptedRequestCount_eq_zero_iff_firstAcceptedArrivalTime_gt
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy) (t : Real)
    (seed : GN21RawCycleSeed)
    (haccepted : ∃ n, gn21RawCycleMark state n seed ∈ sigma)
    (hgap : ∀ n, 0 ≤ gn21RawCycleClock clock n seed)
    (hthreshold : ∀ n,
      n < EconCSLib.Probability.PoissonProcess.canonicalRenewalCount t (seed.1 clock) ↔
        EconCSLib.Probability.PoissonProcess.arrivalTime n (seed.1 clock) ≤ t) :
    gn21RawAcceptedRequestCount clock state sigma t seed = 0 ↔
      t < gn21RawFirstAcceptedArrivalTime clock state sigma seed := by
  classical
  let marks : Nat -> TripLength := fun n => gn21RawCycleMark state n seed
  let index : Nat := AcceptedTripSelection.firstAcceptedIndex sigma marks
  let h : ∃ n, marks n ∈ sigma := by simpa [marks] using haccepted
  have hfirst : marks ∈ AcceptedTripSelection.firstAcceptedEvent sigma (Nat.find h) := by
    rw [AcceptedTripSelection.mem_firstAcceptedEvent_iff]
    refine ⟨Nat.find_spec h, ?_⟩
    intro m hm
    exact Nat.find_min h hm
  have hindex : index = Nat.find h := by
    exact AcceptedTripSelection.firstAcceptedIndex_eq_of_firstSuccessEvent sigma hfirst
  have hindex_accepted : marks index ∈ sigma := by
    rw [hindex]
    exact (AcceptedTripSelection.mem_firstAcceptedEvent_iff sigma marks (Nat.find h)).mp
      hfirst |>.1
  have hindex_noearlier : ∀ m < index, marks m ∉ sigma := by
    intro m hm
    rw [hindex] at hm
    exact (AcceptedTripSelection.mem_firstAcceptedEvent_iff sigma marks (Nat.find h)).mp
      hfirst |>.2 m hm
  have hclock_nonnegative : ∀ n, 0 ≤ (seed.1 clock) n := by
    intro n
    simpa [gn21RawCycleClock] using hgap n
  have hclock_mono : Monotone (fun n : Nat =>
      EconCSLib.Probability.PoissonProcess.arrivalTime n (seed.1 clock)) :=
    EconCSLib.Probability.PoissonProcess.arrivalTime_mono_of_nonnegative
      (seed.1 clock) hclock_nonnegative
  change gn21RawAcceptedRequestCount clock state sigma t seed = 0 ↔
    t < EconCSLib.Probability.PoissonProcess.arrivalTime index (seed.1 clock)
  constructor
  · intro hzero
    by_contra hnot
    have htime_le : EconCSLib.Probability.PoissonProcess.arrivalTime index (seed.1 clock) ≤ t :=
      le_of_not_gt hnot
    have hindex_lt : index <
        EconCSLib.Probability.PoissonProcess.canonicalRenewalCount t (seed.1 clock) :=
      (hthreshold index).mpr htime_le
    have hreject := (rawAcceptedRequestCount_eq_zero_iff clock state sigma t seed).mp hzero
    exact hreject ⟨index, hindex_lt⟩ (by simpa [marks] using hindex_accepted)
  · intro htime
    refine (rawAcceptedRequestCount_eq_zero_iff clock state sigma t seed).mpr ?_
    intro i himem
    have hindex_le : index ≤ (i : Nat) := by
      by_contra hnot
      have hlt : (i : Nat) < index := Nat.lt_of_not_ge hnot
      exact (hindex_noearlier (i : Nat) hlt) (by simpa [marks] using himem)
    have hi_time : EconCSLib.Probability.PoissonProcess.arrivalTime (i : Nat)
        (seed.1 clock) ≤ t :=
      (hthreshold (i : Nat)).mp i.isLt
    have htime_le : EconCSLib.Probability.PoissonProcess.arrivalTime index
        (seed.1 clock) ≤ t :=
      (hclock_mono hindex_le).trans hi_time
    exact (not_le_of_gt htime) htime_le

/-- At each fixed calendar time, the zero retained-count event and the tail
event of the literal first accepted-arrival time agree almost surely. -/
theorem ae_rawAcceptedRequestCount_eq_zero_iff_firstAcceptedArrivalTime_gt
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
    (t : Real) :
    ∀ᵐ seed ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI,
      gn21RawAcceptedRequestCount clock state sigma t seed = 0 ↔
        t < gn21RawFirstAcceptedArrivalTime clock state sigma seed := by
  have haccepted := ae_rawTripMarkStream_exists_accepted
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass
  have hgap := ae_rawClockStream_nonnegative muI muJ arrivalI arrivalJ
    switchIJ switchJI harrivalI harrivalJ hswitchIJ hswitchJI clock
  have hthreshold := ae_rawClock_count_threshold muI muJ arrivalI arrivalJ
    switchIJ switchJI harrivalI harrivalJ hswitchIJ hswitchJI clock t
  filter_upwards [haccepted, hgap, hthreshold] with seed haccepted hgap hthreshold
  apply rawAcceptedRequestCount_eq_zero_iff_firstAcceptedArrivalTime_gt
    clock state sigma t seed
  · simpa [rawTripMarkStream] using haccepted
  · simpa [rawClockStream] using hgap
  · simpa [rawClockStream] using hthreshold

/-- The literal first accepted-arrival time is nonnegative almost surely under
the raw positive-rate clock model. -/
theorem ae_gn21RawFirstAcceptedArrivalTime_nonnegative
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy) :
    ∀ᵐ seed ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI,
      0 ≤ gn21RawFirstAcceptedArrivalTime clock state sigma seed := by
  have hgap := ae_rawClockStream_nonnegative muI muJ arrivalI arrivalJ
    switchIJ switchJI harrivalI harrivalJ hswitchIJ hswitchJI clock
  filter_upwards [hgap] with seed hgap
  change 0 ≤ EconCSLib.Probability.PoissonProcess.arrivalTime
    (AcceptedTripSelection.firstAcceptedIndex sigma (rawTripMarkStream state seed))
    (rawClockStream clock seed)
  exact EconCSLib.Probability.PoissonProcess.arrivalTime_nonnegative_of_interarrival_nonnegative
    (rawClockStream clock seed) hgap _

/-- The literal first accepted-arrival observable has the exponential survival
probability at every nonnegative deterministic time.  This is obtained from
the actual finite-horizon accepted-count law, not from a separately supplied
thinned clock. -/
theorem gn21RawFirstAcceptedArrivalTime_tail_real
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
    (t : Real) (ht : 0 ≤ t) :
    (Measure.map (gn21RawFirstAcceptedArrivalTime clock state sigma)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)).real
        (Set.Ioi t) =
      (ProbabilityTheory.expMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock *
          singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)).real (Set.Ioi t) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let M := gn21CycleMarkLaw muI muJ state
  let rate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock
  let thinnedRate := rate * singleStateTripMass M sigma
  let mean : ℝ≥0 := NNReal.mk (rate * t) (mul_nonneg
    (rawClockRate_pos arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI clock).le ht) *
    gn21AcceptanceProbability M sigma
  have hrate : 0 < rate := rawClockRate_pos arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI clock
  have hthinnedRate : 0 < thinnedRate := by
    exact mul_pos hrate (by simpa [M] using hmass)
  have htail_event := ae_rawAcceptedRequestCount_eq_zero_iff_firstAcceptedArrivalTime_gt
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI clock state sigma hsigma hmass t
  have htail_set :
      (gn21RawFirstAcceptedArrivalTime clock state sigma ⁻¹' Set.Ioi t) =ᵐ[P]
        {seed | gn21RawAcceptedRequestCount clock state sigma t seed = 0} := by
    filter_upwards [htail_event] with seed hseed
    simpa [Set.mem_preimage] using hseed.symm
  have htail_measure :
      P.real (gn21RawFirstAcceptedArrivalTime clock state sigma ⁻¹' Set.Ioi t) =
        P.real {seed | gn21RawAcceptedRequestCount clock state sigma t seed = 0} := by
    simpa [Measure.real] using congrArg ENNReal.toReal (MeasureTheory.measure_congr htail_set)
  have hcount_law : HasLaw (gn21RawAcceptedRequestCount clock state sigma t)
      (ProbabilityTheory.poissonMeasure mean) P := by
    simpa [P, M, rate, mean] using
      (gn21RawAcceptedRequestCount_hasLaw_poisson_of_sourceMass
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI clock state sigma hsigma t ht)
  have hcount_zero :
      P.real {seed | gn21RawAcceptedRequestCount clock state sigma t seed = 0} =
        (ProbabilityTheory.poissonMeasure mean).real {0} := by
    change (P (gn21RawAcceptedRequestCount clock state sigma t ⁻¹'
      ({0} : Set Nat))).toReal =
        (ProbabilityTheory.poissonMeasure mean).real {0}
    rw [← Measure.map_apply_of_aemeasurable hcount_law.aemeasurable
      (measurableSet_singleton 0)]
    change (P.map (gn21RawAcceptedRequestCount clock state sigma t)).real {0} = _
    rw [hcount_law.map_eq]
  have hmean : (mean : Real) = thinnedRate * t := by
    dsimp [mean, thinnedRate]
    rw [gn21AcceptanceProbability_toReal_eq_singleStateTripMass]
    ring
  let E : EconCSLib.Probability.Exponential.Model := ⟨thinnedRate, hthinnedRate⟩
  have hexp_tail :
      (ProbabilityTheory.expMeasure thinnedRate).real (Set.Ioi t) =
        Real.exp (-(thinnedRate * t)) := by
    simpa [E, EconCSLib.Probability.Exponential.Model.measure] using
      E.measure_Ioi_toReal ht
  calc
    (Measure.map (gn21RawFirstAcceptedArrivalTime clock state sigma) P).real (Set.Ioi t) =
        P.real (gn21RawFirstAcceptedArrivalTime clock state sigma ⁻¹' Set.Ioi t) := by
          rw [MeasureTheory.map_measureReal_apply
            (measurable_gn21RawFirstAcceptedArrivalTime clock state sigma hsigma)
            measurableSet_Ioi]
    _ = P.real {seed | gn21RawAcceptedRequestCount clock state sigma t seed = 0} :=
      htail_measure
    _ = (ProbabilityTheory.poissonMeasure mean).real {0} := hcount_zero
    _ = Real.exp (-(thinnedRate * t)) := by
      rw [ProbabilityTheory.poissonMeasure_real_singleton]
      simp [hmean]
    _ = (ProbabilityTheory.expMeasure thinnedRate).real (Set.Ioi t) := hexp_tail.symm
    _ = (ProbabilityTheory.expMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock *
          singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)).real (Set.Ioi t) := by
      simp [thinnedRate, rate, M]

/-- The first accepted request in the literal GN21 raw marked-Poisson seed
arrives at an exponential time with the source-thinned rate. -/
theorem gn21RawFirstAcceptedArrivalTime_hasLaw_expMeasure
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    HasLaw (gn21RawFirstAcceptedArrivalTime clock state sigma)
      (ProbabilityTheory.expMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock *
          singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let M := gn21CycleMarkLaw muI muJ state
  let rate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock
  let thinnedRate := rate * singleStateTripMass M sigma
  let T := gn21RawFirstAcceptedArrivalTime clock state sigma
  have hrate : 0 < rate := rawClockRate_pos arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI clock
  have hthinnedRate : 0 < thinnedRate := by
    exact mul_pos hrate (by simpa [M] using hmass)
  have hTmeas : Measurable T := by
    simpa [T] using measurable_gn21RawFirstAcceptedArrivalTime clock state sigma hsigma
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  letI : IsProbabilityMeasure (P.map T) :=
    Measure.isProbabilityMeasure_map hTmeas.aemeasurable
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure thinnedRate) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hthinnedRate
  change HasLaw T (ProbabilityTheory.expMeasure thinnedRate) P
  refine ⟨hTmeas.aemeasurable, ?_⟩
  apply Measure.ext_of_Iic
  intro x
  apply (MeasureTheory.measureReal_eq_measureReal_iff).mp
  by_cases hx : 0 ≤ x
  · have htail :
        (P.map T).real (Set.Ioi x) =
          (ProbabilityTheory.expMeasure thinnedRate).real (Set.Ioi x) := by
      simpa [P, M, rate, thinnedRate, T] using
        (gn21RawFirstAcceptedArrivalTime_tail_real
          muI muJ arrivalI arrivalJ switchIJ switchJI
          harrivalI harrivalJ hswitchIJ hswitchJI clock state sigma hsigma hmass x hx)
    have hcomp : (Set.Iic x)ᶜ = Set.Ioi x := by
      ext y
      simp
    have hleft := MeasureTheory.probReal_add_probReal_compl
      (μ := P.map T) (s := Set.Iic x) measurableSet_Iic
    have hright := MeasureTheory.probReal_add_probReal_compl
      (μ := ProbabilityTheory.expMeasure thinnedRate) (s := Set.Iic x)
      measurableSet_Iic
    rw [hcomp] at hleft hright
    linarith
  · have hxlt : x < 0 := lt_of_not_ge hx
    have hTnonneg : ∀ᵐ seed ∂P, 0 ≤ T seed := by
      simpa [P, T] using
        (ae_gn21RawFirstAcceptedArrivalTime_nonnegative
          muI muJ arrivalI arrivalJ switchIJ switchJI
          harrivalI harrivalJ hswitchIJ hswitchJI clock state sigma)
    have hnotmem : ∀ᵐ seed ∂P, seed ∉ T ⁻¹' Set.Iic x := by
      filter_upwards [hTnonneg] with seed hnonneg hmem
      change T seed ≤ x at hmem
      linarith
    have hzero : P (T ⁻¹' Set.Iic x) = 0 :=
      MeasureTheory.measure_eq_zero_iff_ae_notMem.mpr hnotmem
    have hleft : (P.map T).real (Set.Iic x) = 0 := by
      rw [MeasureTheory.map_measureReal_apply hTmeas measurableSet_Iic]
      simp [Measure.real, hzero]
    have hright : (ProbabilityTheory.expMeasure thinnedRate).real (Set.Iic x) = 0 := by
      rw [← ProbabilityTheory.cdf_eq_real,
        ProbabilityTheory.cdf_expMeasure_eq hthinnedRate x, if_neg hx]
    exact hleft.trans hright.symm

end AcceptedArrivalTime

end

end GN21DriverSurgePricing
