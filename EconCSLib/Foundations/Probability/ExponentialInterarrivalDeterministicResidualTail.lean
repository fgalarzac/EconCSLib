import EconCSLib.Foundations.Probability.ExponentialInterarrivalResidualTail

/-!
# Deterministic-clock residual tails for exponential renewal paths

This module proves that the residual interarrival path seen from any
nonnegative deterministic clock time has the original iid exponential law.
The proof decomposes over the countably many possible straddling gaps, applies
the exponential memoryless law on each gap, and sums the resulting factorization.
-/

namespace EconCSLib.Probability.PoissonProcess

open MeasureTheory Filter
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

private def straddleProductSet (s : ℝ) : Set (ℝ × (ℕ → ℝ)) :=
  {p | p.1 ≤ s ∧ s < p.1 + interarrival 0 p.2}

private def straddleResidualTail (s : ℝ) (p : ℝ × (ℕ → ℝ)) : ℕ → ℝ :=
  firstGapResidualTail (s - p.1) p.2

private theorem measurable_straddleProductSet (s : ℝ) :
    MeasurableSet (straddleProductSet s) := by
  exact (measurableSet_le measurable_fst measurable_const).inter
    (measurableSet_lt measurable_const
      (measurable_fst.add ((measurable_interarrival 0).comp measurable_snd)))

private theorem measurable_straddleResidualTail (s : ℝ) :
    Measurable (straddleResidualTail s) := by
  apply measurable_pi_iff.2
  intro k
  cases k with
  | zero =>
      simpa [straddleResidualTail, firstGapResidualTail] using
        ((measurable_interarrival 0).comp measurable_snd).sub
          (measurable_const.sub measurable_fst)
  | succ k =>
      simpa [straddleResidualTail, firstGapResidualTail] using
        (measurable_interarrival (k + 1)).comp measurable_snd

private theorem slice_straddleResidualTail_factorization
    {rate s a : ℝ} (hrate : 0 < rate)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) :
    exponentialInterarrivalMeasure rate
        {ξ | a ≤ s ∧ s < a + interarrival 0 ξ ∧
          firstGapResidualTail (s - a) ξ ∈ B} =
      exponentialInterarrivalMeasure rate B *
        exponentialInterarrivalMeasure rate
          {ξ | a ≤ s ∧ s < a + interarrival 0 ξ} := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  change μ {ξ | a ≤ s ∧ s < a + interarrival 0 ξ ∧
      firstGapResidualTail (s - a) ξ ∈ B} =
    μ B * μ {ξ | a ≤ s ∧ s < a + interarrival 0 ξ}
  by_cases ha : a ≤ s
  · let elapsed : ℝ := s - a
    have helapsed : 0 ≤ elapsed := by
      dsimp [elapsed]
      linarith
    have hsurvival : {ξ | elapsed < interarrival 0 ξ} =
        {ξ | a ≤ s ∧ s < a + interarrival 0 ξ} := by
      ext ξ
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hξ
        exact ⟨ha, by dsimp [elapsed] at hξ; linarith⟩
      · rintro ⟨_, hξ⟩
        dsimp [elapsed]
        linarith
    have hleft : {ξ | a ≤ s ∧ s < a + interarrival 0 ξ ∧
        firstGapResidualTail (s - a) ξ ∈ B} =
        {ξ | elapsed < interarrival 0 ξ} ∩
          firstGapResidualTail elapsed ⁻¹' B := by
      ext ξ
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨_, hstraddle, hBξ⟩
        exact ⟨by dsimp [elapsed]; linarith, by simpa [elapsed] using hBξ⟩
      · rintro ⟨hsurvive, hBξ⟩
        exact ⟨ha, by dsimp [elapsed] at hsurvive; linarith,
          by simpa [elapsed] using hBξ⟩
    have hsurvival_measure :
        μ {ξ | elapsed < interarrival 0 ξ} =
          ProbabilityTheory.expMeasure rate (Set.Ioi elapsed) := by
      calc
        μ {ξ | elapsed < interarrival 0 ξ} =
            μ ((interarrival 0) ⁻¹' Set.Ioi elapsed) := by rfl
        _ = (μ.map (interarrival 0)) (Set.Ioi elapsed) := by
            exact (Measure.map_apply (measurable_interarrival 0) measurableSet_Ioi).symm
        _ = ProbabilityTheory.expMeasure rate (Set.Ioi elapsed) := by
            simpa [μ] using congrArg (fun m : Measure ℝ => m (Set.Ioi elapsed))
              (interarrival_hasLaw hrate 0).map_eq
    have hmap := firstGapResidualTail_restrict_map_eq_smul hrate helapsed
    have hresidual :
        μ ({ξ | elapsed < interarrival 0 ξ} ∩ firstGapResidualTail elapsed ⁻¹' B) =
          μ {ξ | elapsed < interarrival 0 ξ} * μ B := by
      calc
        μ ({ξ | elapsed < interarrival 0 ξ} ∩ firstGapResidualTail elapsed ⁻¹' B) =
            (μ.restrict {ξ | elapsed < interarrival 0 ξ})
              (firstGapResidualTail elapsed ⁻¹' B) := by
              rw [Measure.restrict_apply]
              · rw [Set.inter_comm]
              · exact (measurable_firstGapResidualTail elapsed) hB
        _ = ((μ.restrict {ξ | elapsed < interarrival 0 ξ}).map
              (firstGapResidualTail elapsed)) B := by
              rw [Measure.map_apply (measurable_firstGapResidualTail elapsed) hB]
        _ = (ProbabilityTheory.expMeasure rate (Set.Ioi elapsed) • μ) B := by
              simpa [μ] using congrArg (fun m : Measure (ℕ → ℝ) => m B) hmap
        _ = ProbabilityTheory.expMeasure rate (Set.Ioi elapsed) * μ B := by simp
        _ = μ {ξ | elapsed < interarrival 0 ξ} * μ B := by
              rw [hsurvival_measure]
    calc
      μ {ξ | a ≤ s ∧ s < a + interarrival 0 ξ ∧
          firstGapResidualTail (s - a) ξ ∈ B} =
          μ ({ξ | elapsed < interarrival 0 ξ} ∩ firstGapResidualTail elapsed ⁻¹' B) := by
            rw [hleft]
      _ = μ {ξ | elapsed < interarrival 0 ξ} * μ B := hresidual
      _ = μ B * μ {ξ | a ≤ s ∧ s < a + interarrival 0 ξ} := by
            rw [hsurvival]
            ac_rfl
  · have hleft_empty : {ξ | a ≤ s ∧ s < a + interarrival 0 ξ ∧
        firstGapResidualTail (s - a) ξ ∈ B} = ∅ := by
      ext ξ
      simp [ha]
    have hright_empty : {ξ | a ≤ s ∧ s < a + interarrival 0 ξ} = ∅ := by
      ext ξ
      simp [ha]
    rw [hleft_empty, hright_empty]
    simp

private theorem product_straddleResidualTail_factorization
    {rate s : ℝ} (hrate : 0 < rate) (ν : Measure ℝ)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) :
    (ν.prod (exponentialInterarrivalMeasure rate))
        {p | p ∈ straddleProductSet s ∧ straddleResidualTail s p ∈ B} =
      (exponentialInterarrivalMeasure rate B) *
        (ν.prod (exponentialInterarrivalMeasure rate)) (straddleProductSet s) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  letI : IsProbabilityMeasure μ := by
    simpa [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hEvent : MeasurableSet {p | p ∈ straddleProductSet s ∧
      straddleResidualTail s p ∈ B} :=
    (measurable_straddleProductSet s).inter ((measurable_straddleResidualTail s) hB)
  rw [Measure.prod_apply hEvent, Measure.prod_apply (measurable_straddleProductSet s)]
  have hslice : ∀ a : ℝ,
      μ (Prod.mk a ⁻¹' {p | p ∈ straddleProductSet s ∧
        straddleResidualTail s p ∈ B}) =
        μ B * μ (Prod.mk a ⁻¹' straddleProductSet s) := by
    intro a
    have hpreEvent :
        Prod.mk a ⁻¹' {p | p ∈ straddleProductSet s ∧
          straddleResidualTail s p ∈ B} =
          {ξ | a ≤ s ∧ s < a + interarrival 0 ξ ∧
            firstGapResidualTail (s - a) ξ ∈ B} := by
      ext ξ
      simp [straddleProductSet, straddleResidualTail, and_assoc]
    have hpreStraddle : Prod.mk a ⁻¹' straddleProductSet s =
        {ξ | a ≤ s ∧ s < a + interarrival 0 ξ} := by
      ext ξ
      simp [straddleProductSet]
    rw [hpreEvent, hpreStraddle]
    exact slice_straddleResidualTail_factorization hrate B hB
  calc
    ∫⁻ a, μ (Prod.mk a ⁻¹' {p | p ∈ straddleProductSet s ∧
        straddleResidualTail s p ∈ B}) ∂ν =
        ∫⁻ a, μ B * μ (Prod.mk a ⁻¹' straddleProductSet s) ∂ν := by
          exact lintegral_congr hslice
    _ = μ B * ∫⁻ a, μ (Prod.mk a ⁻¹' straddleProductSet s) ∂ν := by
          exact lintegral_const_mul' _ _ (measure_ne_top _ _)

private def fixedStraddleEvent (s : ℝ) (n : ℕ) : Set (ℕ → ℝ) :=
  {ω | arrivalPrefix n ω ≤ s ∧ s < arrivalTime n ω}

private def fixedStraddleFirstGapResidualEvent
    (s : ℝ) (n : ℕ) (B : Set (ℕ → ℝ)) : Set (ℕ → ℝ) :=
  {ω | fixedStraddleEvent s n ω ∧
    firstGapResidualTail (s - arrivalPrefix n ω) (futureInterarrival n ω) ∈ B}

private def renewalCountFiber (s : ℝ) (n : ℕ) : Set (ℕ → ℝ) :=
  {ω | canonicalRenewalCount s ω = n}

private theorem residualTail_eq_firstGapResidualTail_of_count_eq
    (s : ℝ) (ω : ℕ → ℝ) (n : ℕ)
    (hcount : canonicalRenewalCount s ω = n) :
    residualTail s ω =
      firstGapResidualTail (s - arrivalPrefix n ω) (futureInterarrival n ω) := by
  funext k
  cases k with
  | zero =>
      simp [residualTail, firstGapResidualTail, hcount, arrivalTime, arrivalPrefix,
        futureInterarrival, interarrival, Finset.sum_range_succ]
      ring
  | succ k =>
      simp [residualTail, firstGapResidualTail, hcount, futureInterarrival, interarrival]

private theorem arrivalPrefix_futureInterarrival_hasLaw_prod
    {rate : ℝ} (hrate : 0 < rate) (n : ℕ) :
    ProbabilityTheory.HasLaw
      (fun ω : ℕ → ℝ => (arrivalPrefix n ω, futureInterarrival n ω))
      ((Measure.map (arrivalPrefix n) (exponentialInterarrivalMeasure rate)).prod
        (exponentialInterarrivalMeasure rate))
      (exponentialInterarrivalMeasure rate) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let X : (ℕ → ℝ) → ℝ := arrivalPrefix n
  let Y : (ℕ → ℝ) → (ℕ → ℝ) := futureInterarrival n
  letI : IsProbabilityMeasure μ := by
    simpa [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hX : Measurable X := by simpa [X] using measurable_arrivalPrefix n
  have hY : Measurable Y := by
    simpa [Y] using measurable_pi_iff.2 (fun k => measurable_futureInterarrival n k)
  have hIndep : ProbabilityTheory.IndepFun X Y μ := by
    simpa [μ, X, Y] using arrivalPrefix_indep_futureInterarrival hrate n
  refine ⟨(hX.prodMk hY).aemeasurable, ?_⟩
  have htail : μ.map Y = μ := by
    simpa [μ, Y] using (futureInterarrival_hasLaw_path hrate n).map_eq
  calc
    μ.map (fun ω => (X ω, Y ω)) = (μ.map X).prod (μ.map Y) :=
      (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
        hX.aemeasurable hY.aemeasurable).mp hIndep
    _ = (μ.map X).prod μ := by rw [htail]

private theorem measurableSet_fixedStraddleEvent (s : ℝ) (n : ℕ) :
    MeasurableSet (fixedStraddleEvent s n) := by
  exact (measurableSet_le (measurable_arrivalPrefix n) measurable_const).inter
    (measurableSet_lt measurable_const (measurable_arrivalTime n))

private theorem measurableSet_fixedStraddleFirstGapResidualEvent
    (s : ℝ) (n : ℕ) (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) :
    MeasurableSet (fixedStraddleFirstGapResidualEvent s n B) := by
  have htail : Measurable (fun ω : ℕ → ℝ =>
      firstGapResidualTail (s - arrivalPrefix n ω) (futureInterarrival n ω)) := by
    apply measurable_pi_iff.2
    intro k
    cases k with
    | zero =>
        simpa [firstGapResidualTail] using
          ((measurable_interarrival 0).comp
            (measurable_pi_iff.2 fun j => measurable_futureInterarrival n j)).sub
              (measurable_const.sub (measurable_arrivalPrefix n))
    | succ k =>
        simpa [firstGapResidualTail] using
          (measurable_interarrival (k + 1)).comp
            (measurable_pi_iff.2 fun j => measurable_futureInterarrival n j)
  exact (measurableSet_fixedStraddleEvent s n).inter (htail hB)

private theorem measure_fixedStraddleEvent_eq_product
    {rate : ℝ} (hrate : 0 < rate) (s : ℝ) (n : ℕ) :
    exponentialInterarrivalMeasure rate (fixedStraddleEvent s n) =
      ((Measure.map (arrivalPrefix n) (exponentialInterarrivalMeasure rate)).prod
        (exponentialInterarrivalMeasure rate)) (straddleProductSet s) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let f : (ℕ → ℝ) → ℝ × (ℕ → ℝ) :=
    fun ω => (arrivalPrefix n ω, futureInterarrival n ω)
  have hf : Measurable f := by
    exact (measurable_arrivalPrefix n).prodMk
      (measurable_pi_iff.2 fun k => measurable_futureInterarrival n k)
  have hpreimage : f ⁻¹' straddleProductSet s = fixedStraddleEvent s n := by
    ext ω
    simp only [f, straddleProductSet, Set.mem_preimage, Set.mem_setOf_eq]
    have htail : interarrival 0 (futureInterarrival n ω) = interarrival n ω := by rfl
    rw [htail]
    simp [fixedStraddleEvent, arrivalTime, arrivalPrefix, Finset.sum_range_succ]
  calc
    μ (fixedStraddleEvent s n) = μ (f ⁻¹' straddleProductSet s) := by rw [hpreimage]
    _ = (Measure.map f μ) (straddleProductSet s) := by
      symm
      exact Measure.map_apply hf (measurable_straddleProductSet s)
    _ = ((Measure.map (arrivalPrefix n) μ).prod μ) (straddleProductSet s) := by
      rw [(arrivalPrefix_futureInterarrival_hasLaw_prod hrate n).map_eq]

private theorem measure_fixedStraddleFirstGapResidualEvent_eq_product
    {rate : ℝ} (hrate : 0 < rate) (s : ℝ) (n : ℕ)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) :
    exponentialInterarrivalMeasure rate (fixedStraddleFirstGapResidualEvent s n B) =
      ((Measure.map (arrivalPrefix n) (exponentialInterarrivalMeasure rate)).prod
        (exponentialInterarrivalMeasure rate))
        {p | p ∈ straddleProductSet s ∧ straddleResidualTail s p ∈ B} := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let f : (ℕ → ℝ) → ℝ × (ℕ → ℝ) :=
    fun ω => (arrivalPrefix n ω, futureInterarrival n ω)
  have hf : Measurable f := by
    exact (measurable_arrivalPrefix n).prodMk
      (measurable_pi_iff.2 fun k => measurable_futureInterarrival n k)
  have hpreimage : f ⁻¹' {p | p ∈ straddleProductSet s ∧
      straddleResidualTail s p ∈ B} =
      fixedStraddleFirstGapResidualEvent s n B := by
    ext ω
    change
      ((arrivalPrefix n ω ≤ s ∧
          s < arrivalPrefix n ω + interarrival 0 (futureInterarrival n ω)) ∧
        firstGapResidualTail (s - arrivalPrefix n ω) (futureInterarrival n ω) ∈ B) ↔
      ((arrivalPrefix n ω ≤ s ∧ s < arrivalTime n ω) ∧
        firstGapResidualTail (s - arrivalPrefix n ω) (futureInterarrival n ω) ∈ B)
    have htail : interarrival 0 (futureInterarrival n ω) = interarrival n ω := by rfl
    have harrival : arrivalTime n ω =
        arrivalPrefix n ω + interarrival n ω := by
      simp [arrivalTime, arrivalPrefix, Finset.sum_range_succ]
    rw [htail, harrival]
  calc
    μ (fixedStraddleFirstGapResidualEvent s n B) =
        μ (f ⁻¹' {p | p ∈ straddleProductSet s ∧ straddleResidualTail s p ∈ B}) := by
          rw [hpreimage]
    _ = (Measure.map f μ) {p | p ∈ straddleProductSet s ∧ straddleResidualTail s p ∈ B} := by
      symm
      exact Measure.map_apply hf
        ((measurable_straddleProductSet s).inter ((measurable_straddleResidualTail s) hB))
    _ = ((Measure.map (arrivalPrefix n) μ).prod μ)
        {p | p ∈ straddleProductSet s ∧ straddleResidualTail s p ∈ B} := by
          rw [(arrivalPrefix_futureInterarrival_hasLaw_prod hrate n).map_eq]

private theorem measure_fixedStraddleFirstGapResidualEvent_factorization
    {rate : ℝ} (hrate : 0 < rate) (s : ℝ) (n : ℕ)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) :
    exponentialInterarrivalMeasure rate (fixedStraddleFirstGapResidualEvent s n B) =
      exponentialInterarrivalMeasure rate B *
        exponentialInterarrivalMeasure rate (fixedStraddleEvent s n) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let ν : Measure ℝ := μ.map (arrivalPrefix n)
  calc
    μ (fixedStraddleFirstGapResidualEvent s n B) =
        (ν.prod μ) {p | p ∈ straddleProductSet s ∧ straddleResidualTail s p ∈ B} := by
          simpa [μ, ν] using
            measure_fixedStraddleFirstGapResidualEvent_eq_product hrate s n B hB
    _ = μ B * (ν.prod μ) (straddleProductSet s) := by
          exact product_straddleResidualTail_factorization hrate ν B hB
    _ = μ B * μ (fixedStraddleEvent s n) := by
          rw [measure_fixedStraddleEvent_eq_product hrate s n]

private theorem fixedStraddleEvent_iff_canonicalRenewalCount_eq
    (s : ℝ) (hs : 0 ≤ s) (ω : ℕ → ℝ)
    (hdiv : Tendsto (fun n : ℕ => arrivalTime n ω) atTop atTop)
    (hpos : ∀ i : ℕ, 0 < interarrival i ω) (n : ℕ) :
    fixedStraddleEvent s n ω ↔ canonicalRenewalCount s ω = n := by
  cases n with
  | zero =>
      constructor
      · intro h
        rw [canonicalRenewalCount_eq_zero_iff]
        exact Or.inl h.2
      · intro h
        rw [canonicalRenewalCount_eq_zero_iff] at h
        rcases h with h | h
        · exact ⟨by simp [arrivalPrefix, hs], h⟩
        · exact (h (exists_arrivalTime_gt_of_tendsto_atTop ω hdiv s)).elim
  | succ n =>
      constructor
      · rintro ⟨hpref, hupper⟩
        apply (canonicalRenewalCount_eq_succ_iff s ω n).mpr
        refine ⟨hupper, ?_⟩
        intro m hm hsm
        have hle : arrivalTime m ω ≤ arrivalTime n ω :=
          (arrivalTime_strictMono_of_positive ω hpos).monotone
            (Nat.le_of_lt_succ hm)
        have hpref' : arrivalTime n ω ≤ s := by
          simpa [fixedStraddleEvent, arrivalPrefix] using hpref
        exact (not_lt_of_ge (hle.trans hpref')) hsm
      · intro h
        rw [canonicalRenewalCount_eq_succ_iff] at h
        rcases h with ⟨hupper, hbefore⟩
        constructor
        · have hnot : ¬ s < arrivalTime n ω :=
            hbefore n (Nat.lt_succ_self n)
          simpa [fixedStraddleEvent, arrivalPrefix] using le_of_not_gt hnot
        · exact hupper

private theorem ae_fixedStraddleEvent_eq_renewalCountFiber
    {rate s : ℝ} (hrate : 0 < rate) (hs : 0 ≤ s) (n : ℕ) :
    fixedStraddleEvent s n =ᵐ[exponentialInterarrivalMeasure rate]
      renewalCountFiber s n := by
  filter_upwards [ae_arrivalTime_tendsto_atTop hrate,
    ae_all_interarrival_positive hrate] with ω hdiv hpos
  apply propext
  exact fixedStraddleEvent_iff_canonicalRenewalCount_eq s hs ω hdiv hpos n

private def renewalCountResidualTailFiber
    (s : ℝ) (n : ℕ) (B : Set (ℕ → ℝ)) : Set (ℕ → ℝ) :=
  {ω | canonicalRenewalCount s ω = n ∧ residualTail s ω ∈ B}

private theorem ae_fixedStraddleFirstGapResidualEvent_eq_renewalCountResidualTailFiber
    {rate s : ℝ} (hrate : 0 < rate) (hs : 0 ≤ s) (n : ℕ)
    (B : Set (ℕ → ℝ)) :
    fixedStraddleFirstGapResidualEvent s n B =ᵐ[exponentialInterarrivalMeasure rate]
      renewalCountResidualTailFiber s n B := by
  filter_upwards [ae_fixedStraddleEvent_eq_renewalCountFiber hrate hs n] with ω hstraddle
  apply propext
  constructor
  · rintro ⟨hfixed, hfirst⟩
    have hcount : canonicalRenewalCount s ω = n := hstraddle.mp hfixed
    refine ⟨hcount, ?_⟩
    rw [residualTail_eq_firstGapResidualTail_of_count_eq s ω n hcount]
    exact hfirst
  · rintro ⟨hcount, hresidual⟩
    refine ⟨hstraddle.mpr hcount, ?_⟩
    rw [← residualTail_eq_firstGapResidualTail_of_count_eq s ω n hcount]
    exact hresidual

private theorem measure_renewalCountResidualTailFiber_factorization
    {rate s : ℝ} (hrate : 0 < rate) (hs : 0 ≤ s) (n : ℕ)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) :
    exponentialInterarrivalMeasure rate (renewalCountResidualTailFiber s n B) =
      exponentialInterarrivalMeasure rate B *
        exponentialInterarrivalMeasure rate (renewalCountFiber s n) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  calc
    μ (renewalCountResidualTailFiber s n B) =
        μ (fixedStraddleFirstGapResidualEvent s n B) := by
          exact (measure_congr
            (ae_fixedStraddleFirstGapResidualEvent_eq_renewalCountResidualTailFiber
              hrate hs n B)).symm
    _ = μ B * μ (fixedStraddleEvent s n) := by
          simpa [μ] using
            measure_fixedStraddleFirstGapResidualEvent_factorization hrate s n B hB
    _ = μ B * μ (renewalCountFiber s n) := by
          rw [measure_congr (ae_fixedStraddleEvent_eq_renewalCountFiber hrate hs n)]

private theorem measurableSet_renewalCountFiber (s : ℝ) (n : ℕ) :
    MeasurableSet (renewalCountFiber s n) := by
  exact (measurable_canonicalRenewalCount s) (measurableSet_singleton n)

private theorem measurableSet_renewalCountResidualTailFiber
    (s : ℝ) (n : ℕ) (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) :
    MeasurableSet (renewalCountResidualTailFiber s n B) := by
  exact (measurableSet_renewalCountFiber s n).inter ((measurable_residualTail s) hB)

private theorem renewalCountFiber_pairwiseDisjoint (s : ℝ) :
    Pairwise (Function.onFun Disjoint (renewalCountFiber s)) := by
  intro n m hnm
  refine Set.disjoint_left.2 ?_
  intro ω hn hm
  exact hnm (hn.symm.trans hm)

private theorem renewalCountResidualTailFiber_pairwiseDisjoint
    (s : ℝ) (B : Set (ℕ → ℝ)) :
    Pairwise (Function.onFun Disjoint (renewalCountResidualTailFiber s · B)) := by
  intro n m hnm
  refine Set.disjoint_left.2 ?_
  intro ω hn hm
  exact hnm (hn.1.symm.trans hm.1)

private theorem iUnion_renewalCountFiber_eq_univ (s : ℝ) :
    ⋃ n, renewalCountFiber s n = Set.univ := by
  ext ω
  constructor
  · intro _
    simp
  · intro _
    exact Set.mem_iUnion.2 ⟨canonicalRenewalCount s ω, rfl⟩

private theorem iUnion_renewalCountResidualTailFiber_eq_preimage
    (s : ℝ) (B : Set (ℕ → ℝ)) :
    ⋃ n, renewalCountResidualTailFiber s n B = residualTail s ⁻¹' B := by
  ext ω
  simp [renewalCountResidualTailFiber]

private theorem tsum_measure_renewalCountFiber
    {rate s : ℝ} (hrate : 0 < rate) :
    ∑' n : ℕ, exponentialInterarrivalMeasure rate (renewalCountFiber s n) = 1 := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  letI : IsProbabilityMeasure μ := by
    simpa [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  calc
    ∑' n : ℕ, μ (renewalCountFiber s n) =
        μ (⋃ n : ℕ, renewalCountFiber s n) := by
          symm
          exact measure_iUnion (renewalCountFiber_pairwiseDisjoint s)
            (measurableSet_renewalCountFiber s)
    _ = μ Set.univ := by rw [iUnion_renewalCountFiber_eq_univ]
    _ = 1 := measure_univ

/-- The residual interarrival path observed at a nonnegative deterministic
clock time has the original iid exponential law. -/
theorem residualTail_hasLaw_path
    {rate s : ℝ} (hrate : 0 < rate) (hs : 0 ≤ s) :
    ProbabilityTheory.HasLaw (residualTail s)
      (exponentialInterarrivalMeasure rate) (exponentialInterarrivalMeasure rate) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  letI : IsProbabilityMeasure μ := by
    simpa [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  refine ⟨(measurable_residualTail s).aemeasurable, ?_⟩
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply (measurable_residualTail s) hB]
  change μ (residualTail s ⁻¹' B) = μ B
  calc
    μ (residualTail s ⁻¹' B) =
        μ (⋃ n : ℕ, renewalCountResidualTailFiber s n B) := by
          rw [iUnion_renewalCountResidualTailFiber_eq_preimage]
    _ = ∑' n : ℕ, μ (renewalCountResidualTailFiber s n B) := by
          exact measure_iUnion (renewalCountResidualTailFiber_pairwiseDisjoint s B)
            (fun n => measurableSet_renewalCountResidualTailFiber s n B hB)
    _ = ∑' n : ℕ, μ B * μ (renewalCountFiber s n) := by
          exact tsum_congr
            (measure_renewalCountResidualTailFiber_factorization hrate hs · B hB)
    _ = μ B * ∑' n : ℕ, μ (renewalCountFiber s n) := by
          exact ENNReal.tsum_mul_left
    _ = μ B * 1 := by rw [tsum_measure_renewalCountFiber hrate]
    _ = μ B := by rw [mul_one]

/-- The count accumulated by a nonnegative deterministic clock time is
independent of the complete residual interarrival path after that time. -/
theorem canonicalRenewalCount_indep_residualTail
    {rate s : ℝ} (hrate : 0 < rate) (hs : 0 ≤ s) :
    ProbabilityTheory.IndepFun (canonicalRenewalCount s) (residualTail s)
      (exponentialInterarrivalMeasure rate) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  letI : IsProbabilityMeasure μ := by
    simpa [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul]
  intro A B hA hB
  let pieces : {n : ℕ // n ∈ A} → Set (ℕ → ℝ) :=
    fun n => renewalCountResidualTailFiber s n.1 B
  let counts : {n : ℕ // n ∈ A} → Set (ℕ → ℝ) :=
    fun n => renewalCountFiber s n.1
  have hpieces_union :
      ⋃ n : {n : ℕ // n ∈ A}, pieces n =
        (canonicalRenewalCount s) ⁻¹' A ∩ residualTail s ⁻¹' B := by
    ext ω
    constructor
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨n, hn⟩
      change canonicalRenewalCount s ω = n.1 ∧ residualTail s ω ∈ B at hn
      refine ⟨?_, hn.2⟩
      change canonicalRenewalCount s ω ∈ A
      rw [hn.1]
      exact n.2
    · rintro ⟨hAω, hBω⟩
      apply Set.mem_iUnion.2
      refine ⟨⟨canonicalRenewalCount s ω, hAω⟩, ?_⟩
      change canonicalRenewalCount s ω = canonicalRenewalCount s ω ∧ residualTail s ω ∈ B
      exact ⟨rfl, hBω⟩
  have hpieces_disjoint : Pairwise (Function.onFun Disjoint pieces) := by
    intro n m hnm
    refine Set.disjoint_left.2 ?_
    intro ω hn hm
    change canonicalRenewalCount s ω = n.1 ∧ residualTail s ω ∈ B at hn
    change canonicalRenewalCount s ω = m.1 ∧ residualTail s ω ∈ B at hm
    exact hnm (Subtype.ext (hn.1.symm.trans hm.1))
  have hpieces_meas : ∀ n : {n : ℕ // n ∈ A}, MeasurableSet (pieces n) := by
    intro n
    exact measurableSet_renewalCountResidualTailFiber s n.1 B hB
  have hcounts_union :
      ⋃ n : {n : ℕ // n ∈ A}, counts n = (canonicalRenewalCount s) ⁻¹' A := by
    ext ω
    constructor
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨n, hn⟩
      change canonicalRenewalCount s ω = n.1 at hn
      change canonicalRenewalCount s ω ∈ A
      rw [hn]
      exact n.2
    · intro hAω
      apply Set.mem_iUnion.2
      refine ⟨⟨canonicalRenewalCount s ω, hAω⟩, ?_⟩
      change canonicalRenewalCount s ω = canonicalRenewalCount s ω
      rfl
  have hcounts_disjoint : Pairwise (Function.onFun Disjoint counts) := by
    intro n m hnm
    refine Set.disjoint_left.2 ?_
    intro ω hn hm
    change canonicalRenewalCount s ω = n.1 at hn
    change canonicalRenewalCount s ω = m.1 at hm
    exact hnm (Subtype.ext (hn.symm.trans hm))
  have hcounts_meas : ∀ n : {n : ℕ // n ∈ A}, MeasurableSet (counts n) := by
    intro n
    exact measurableSet_renewalCountFiber s n.1
  have hresidual : μ (residualTail s ⁻¹' B) = μ B := by
    calc
      μ (residualTail s ⁻¹' B) = (μ.map (residualTail s)) B := by
        exact (Measure.map_apply (measurable_residualTail s) hB).symm
      _ = μ B := by
        simpa [μ] using congrArg (fun ν : Measure (ℕ → ℝ) => ν B)
          (residualTail_hasLaw_path hrate hs).map_eq
  calc
    μ ((canonicalRenewalCount s) ⁻¹' A ∩ residualTail s ⁻¹' B) =
        μ (⋃ n : {n : ℕ // n ∈ A}, pieces n) := by
          rw [hpieces_union]
    _ = ∑' n : {n : ℕ // n ∈ A}, μ (pieces n) := by
          exact measure_iUnion hpieces_disjoint hpieces_meas
    _ = ∑' n : {n : ℕ // n ∈ A}, μ B * μ (counts n) := by
          apply tsum_congr
          intro n
          simpa [pieces, counts] using
            measure_renewalCountResidualTailFiber_factorization hrate hs n.1 B hB
    _ = μ B * ∑' n : {n : ℕ // n ∈ A}, μ (counts n) := by
          exact ENNReal.tsum_mul_left
    _ = μ B * μ (⋃ n : {n : ℕ // n ∈ A}, counts n) := by
          rw [measure_iUnion hcounts_disjoint hcounts_meas]
    _ = μ B * μ ((canonicalRenewalCount s) ⁻¹' A) := by rw [hcounts_union]
    _ = μ ((canonicalRenewalCount s) ⁻¹' A) * μ (residualTail s ⁻¹' B) := by
          rw [hresidual]
          ac_rfl

/-- The count accumulated by time `s` is independent of the count increment
over the following deterministic interval of length `h`. -/
theorem canonicalRenewalCount_indep_increment
    {rate s h : ℝ} (hrate : 0 < rate) (hs : 0 ≤ s) (hh : 0 ≤ h) :
    ProbabilityTheory.IndepFun (canonicalRenewalCount s)
      (fun ω => canonicalRenewalCount (s + h) ω - canonicalRenewalCount s ω)
      (exponentialInterarrivalMeasure rate) := by
  have hcomp : ProbabilityTheory.IndepFun (canonicalRenewalCount s)
      (fun ω => canonicalRenewalCount h (residualTail s ω))
      (exponentialInterarrivalMeasure rate) := by
    simpa [Function.comp_def] using
      (canonicalRenewalCount_indep_residualTail hrate hs).comp
        measurable_id (measurable_canonicalRenewalCount h)
  have htail_eq_increment :
      (fun ω => canonicalRenewalCount h (residualTail s ω)) =ᵐ[
        exponentialInterarrivalMeasure rate]
        fun ω => canonicalRenewalCount (s + h) ω - canonicalRenewalCount s ω := by
    filter_upwards [ae_canonicalRenewalCount_increment_eq_residualTailCount hrate s h hh]
      with ω hω
    exact hω.symm
  exact hcomp.congr (Filter.Eventually.of_forall fun _ => rfl)
    htail_eq_increment

/-- A canonical exponential renewal count has Poisson-distributed increments
over every nonnegative deterministic interval. -/
theorem canonicalRenewalCount_increment_hasLaw_poisson
    {rate s h : ℝ} (hrate : 0 < rate) (hs : 0 ≤ s) (hh : 0 ≤ h) :
    ProbabilityTheory.HasLaw
      (fun ω => canonicalRenewalCount (s + h) ω - canonicalRenewalCount s ω)
      (ProbabilityTheory.poissonMeasure
        (⟨rate * h, mul_nonneg hrate.le hh⟩ : ℝ≥0))
      (exponentialInterarrivalMeasure rate) := by
  exact canonicalRenewalCount_increment_hasLaw_poisson_of_residualTail_hasLaw
    hrate s h hh (residualTail_hasLaw_path hrate hs)

end
end EconCSLib.Probability.PoissonProcess
