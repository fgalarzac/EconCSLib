import LG21TestOptionalPolicies.ObservedAccessReportRequiredBaseMassPromotion

/-!
# Reporter-zero base-region support for observed-access report-required testing

This small bridge exposes the measure fact used by the local candidate
argument: on a measurable base region whose current taking fibre has zero
mass, the corresponding current source taking event has zero mass.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-- The reporter-zero region produced by the global no-take split is
measurable whenever the current full-public action rule is measurable. -/
theorem lg21_reportRequired_zeroReporterBaseRegion_measurable
    {Base : Type*} [MeasurableSpace Base]
    (skillKernel : Kernel Base ℝ) [IsMarkovKernel skillKernel]
    (take : Base → ℝ → Bool)
    (htake : Measurable (fun profileSkill : Base × ℝ =>
      take profileSkill.1 profileSkill.2)) :
    MeasurableSet
      (Function.support
        (selectionMass skillKernel
          (lg21ReportRequiredFullPublicNoTakeSet take)) ∩
        {base | selectionMass skillKernel
          (lg21ReportRequiredFullPublicTakeSet take) base = 0}) := by
  have htakeEvent : MeasurableSet
      (lg21ReportRequiredFullPublicTakeSet take) :=
    lg21ReportRequiredFullPublicTakeSet_measurable take htake
  have hnoTakeEvent : MeasurableSet
      (lg21ReportRequiredFullPublicNoTakeSet take) :=
    lg21ReportRequiredFullPublicNoTakeSet_measurable take htake
  have htakeMass : Measurable
      (selectionMass skillKernel (lg21ReportRequiredFullPublicTakeSet take)) :=
    selectionMass_measurable htakeEvent
  have hnoTakeMass : Measurable
      (selectionMass skillKernel (lg21ReportRequiredFullPublicNoTakeSet take)) :=
    selectionMass_measurable hnoTakeEvent
  have hnoTakeSupport : MeasurableSet (Function.support
      (selectionMass skillKernel
        (lg21ReportRequiredFullPublicNoTakeSet take))) := by
    simpa only [Function.support, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff] using
      hnoTakeMass ((measurableSet_singleton (0 : ℝ≥0∞)).compl)
  have htakeZero : MeasurableSet {base | selectionMass skillKernel
      (lg21ReportRequiredFullPublicTakeSet take) base = 0} := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using
      htakeMass (measurableSet_singleton (0 : ℝ≥0∞))
  exact hnoTakeSupport.inter htakeZero

/-- If every base fibre in a measurable region has zero current taking mass,
then the product source law assigns zero mass to current takers in that
region.  This is stated for an arbitrary Markov skill kernel; the Gaussian
specialization is supplied separately by the source factorization. -/
theorem lg21_reportRequired_compProd_currentTake_mass_zero_on_region
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [SFinite baseLaw]
    (skillKernel : Kernel Base ℝ) [IsMarkovKernel skillKernel]
    (take : Base → ℝ → Bool)
    (htake : Measurable (fun profileSkill : Base × ℝ =>
      take profileSkill.1 profileSkill.2))
    (region : Set Base) (hregion : MeasurableSet region)
    (hzero : ∀ base ∈ region,
      selectionMass skillKernel
        (lg21ReportRequiredFullPublicTakeSet take) base = 0) :
    (baseLaw ⊗ₘ skillKernel)
      ((region ×ˢ Set.univ) ∩ lg21ReportRequiredFullPublicTakeSet take) = 0 := by
  let takeEvent : Set (Base × ℝ) := lg21ReportRequiredFullPublicTakeSet take
  let target : Set (Base × ℝ) := (region ×ˢ Set.univ) ∩ takeEvent
  have htakeEvent : MeasurableSet takeEvent := by
    simpa [takeEvent] using
      (lg21ReportRequiredFullPublicTakeSet_measurable take htake)
  have htarget : MeasurableSet target :=
    (hregion.prod MeasurableSet.univ).inter htakeEvent
  change (baseLaw ⊗ₘ skillKernel) target = 0
  rw [Measure.compProd_apply htarget]
  apply lintegral_eq_zero_of_ae_eq_zero
  exact Filter.Eventually.of_forall (fun base => by
    change skillKernel base (Prod.mk base ⁻¹' target) = 0
    by_cases hbase : base ∈ region
    · have hfibre : Prod.mk base ⁻¹' target = selectedFiber takeEvent base := by
        ext skill
        simp [target, takeEvent, selectedFiber, hbase]
      rw [hfibre]
      simpa [selectionMass, takeEvent] using hzero base hbase
    · have hfibre : Prod.mk base ⁻¹' target = ∅ := by
        ext skill
        simp [target, takeEvent, hbase]
      rw [hfibre]
      simp)

/-- The base marginal of a literal `(base, skill)` source factorization is
the displayed base law.  This is kept next to the region transport because a
positive base region must be promoted using this equality, not a named cohort
or a per-fibre assumption. -/
theorem lg21_reportRequired_source_base_preimage_measure_eq_of_factorization
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega)
    (base : Omega → Base) (skill : Omega → ℝ)
    (hbase : Measurable base) (hskill : Measurable skill)
    (baseLaw : Measure Base) [SFinite baseLaw]
    (skillKernel : Kernel Base ℝ) [IsMarkovKernel skillKernel]
    (hsourceFactor : sourceLaw.map (fun omega => (base omega, skill omega)) =
      baseLaw ⊗ₘ skillKernel)
    (region : Set Base) (hregion : MeasurableSet region) :
    sourceLaw (base ⁻¹' region) = baseLaw region := by
  let observation : Omega → Base × ℝ := fun omega => (base omega, skill omega)
  have hobservation : Measurable observation := hbase.prodMk hskill
  have hbaseMarginal : sourceLaw.map base = baseLaw := by
    calc
      sourceLaw.map base = (sourceLaw.map observation).map Prod.fst := by
        rw [Measure.map_map measurable_fst hobservation]
        rfl
      _ = (baseLaw ⊗ₘ skillKernel).map Prod.fst := by
        rw [show sourceLaw.map observation = baseLaw ⊗ₘ skillKernel by
          simpa [observation] using hsourceFactor]
      _ = baseLaw := by
        exact Measure.fst_compProd _ _
  rw [← hbaseMarginal, Measure.map_apply hbase hregion]

/-- Transport the preceding exact product-law fact through a literal
source `(base, skill)` factorization.  The conclusion is deliberately about
the actual sequential action event, rather than a named strategy subset. -/
theorem lg21_reportRequired_source_currentTake_mass_zero_on_region
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega)
    (base : Omega → Base) (skill : Omega → ℝ)
    (hbase : Measurable base) (hskill : Measurable skill)
    (baseLaw : Measure Base) [SFinite baseLaw]
    (skillKernel : Kernel Base ℝ) [IsMarkovKernel skillKernel]
    (hsourceFactor : sourceLaw.map (fun omega => (base omega, skill omega)) =
      baseLaw ⊗ₘ skillKernel)
    (currentTake : ℝ → Base → Bool)
    (hcurrentTake : Measurable (fun profileSkill : Base × ℝ =>
      currentTake profileSkill.2 profileSkill.1))
    (region : Set Base) (hregion : MeasurableSet region)
    (hzero : ∀ publicBase ∈ region,
      selectionMass skillKernel
        (lg21ReportRequiredFullPublicTakeSet
          (fun publicBase latentSkill => currentTake latentSkill publicBase))
        publicBase = 0) :
    sourceLaw (base ⁻¹' region ∩
      {omega | currentTake (skill omega) (base omega) = true}) = 0 := by
  let take : Base → ℝ → Bool := fun publicBase latentSkill =>
    currentTake latentSkill publicBase
  let observation : Omega → Base × ℝ := fun omega => (base omega, skill omega)
  let target : Set (Base × ℝ) :=
    (region ×ˢ Set.univ) ∩ lg21ReportRequiredFullPublicTakeSet take
  have hobservation : Measurable observation := hbase.prodMk hskill
  have htarget : MeasurableSet target := by
    exact (hregion.prod MeasurableSet.univ).inter
      (lg21ReportRequiredFullPublicTakeSet_measurable take (by
        simpa [take, Function.comp_def] using hcurrentTake))
  have hsourceTarget :
      base ⁻¹' region ∩ {omega | currentTake (skill omega) (base omega) = true} =
        observation ⁻¹' target := by
    ext omega
    change (base omega ∈ region ∧
      currentTake (skill omega) (base omega) = true) ↔
      ((base omega ∈ region ∧ skill omega ∈ Set.univ) ∧
        currentTake (skill omega) (base omega) = true)
    simp
  rw [hsourceTarget, ← Measure.map_apply hobservation htarget]
  rw [show sourceLaw.map observation = baseLaw ⊗ₘ skillKernel by
    simpa [observation] using hsourceFactor]
  exact lg21_reportRequired_compProd_currentTake_mass_zero_on_region
    baseLaw skillKernel take (by simpa [take, Function.comp_def] using hcurrentTake)
    region hregion (by simpa [take] using hzero)

end

end LG21TestOptionalPolicies
