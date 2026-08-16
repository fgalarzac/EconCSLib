import LG21TestOptionalPolicies.SelectedSignalPosteriorBridge

/-!
# Conditional-law invariance under public-observation selection

When a positive-mass branch is selected by an event determined entirely by
the public observation, conditioning the population on that event does not
change the conditional latent law once that observation is known.  This is a
measure-level statement: it does not assign a value to an unselected
observation and does not rely on a strategy or posterior name.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

/--
Normalizing a source population on an event determined by its public
observation commutes with mapping the complete `(observation, latent)` pair.
The selected event remains explicit on the mapped carrier.
-/
theorem lg21_selectedObservation_normalizedRestriction_map_pair
    {Omega Observation Latent : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Observation]
    [MeasurableSpace Latent]
    (law : Measure Omega) (observation : Omega -> Observation)
    (latent : Omega -> Latent) (hobservation : Measurable observation)
    (hlatent : Measurable latent) (selected : Set Observation)
    (hselected : MeasurableSet selected) :
    (lg21NormalizedRestriction law (observation ⁻¹' selected)).map
        (fun omega => (observation omega, latent omega)) =
      lg21NormalizedRestriction
        (law.map (fun omega => (observation omega, latent omega)))
        (selected ×ˢ Set.univ) := by
  let paired : Omega -> Observation × Latent :=
    fun omega => (observation omega, latent omega)
  have hpaired : Measurable paired := hobservation.prodMk hlatent
  have hpairEvent : MeasurableSet (selected ×ˢ (Set.univ : Set Latent)) :=
    hselected.prod MeasurableSet.univ
  have hpreimage : paired ⁻¹' (selected ×ˢ (Set.univ : Set Latent)) =
      observation ⁻¹' selected := by
    ext omega
    simp [paired]
  rw [← hpreimage]
  exact lg21_normalizedRestriction_map_preimage law paired hpaired
    (selected ×ˢ Set.univ) hpairEvent

/--
After restricting to a positive-mass event measurable in the public
observation, the latent regular conditional distribution given that
observation is unchanged almost everywhere under the selected observation
law.  The result has no fibrewise positivity premise and hence does not
invent a conditional value on observations outside the selected branch.
-/
theorem lg21_selectedObservation_condDistrib_latent_eq_raw_ae
    {Omega Observation Latent : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Observation]
    [MeasurableSpace Latent] [StandardBorelSpace Latent] [Nonempty Latent]
    (law : Measure Omega) [IsProbabilityMeasure law] [IsFiniteMeasure law]
    (observation : Omega -> Observation) (latent : Omega -> Latent)
    (hobservation : Measurable observation) (hlatent : Measurable latent)
    (selected : Set Observation) (hselected : MeasurableSet selected)
    (hpositive : 0 < law (observation ⁻¹' selected)) :
    let selectedLaw := lg21NormalizedRestriction law (observation ⁻¹' selected)
    letI : IsProbabilityMeasure selectedLaw :=
      lg21NormalizedRestriction_isProbability law (observation ⁻¹' selected)
        (ne_of_gt hpositive) (measure_ne_top _ _)
    letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
    condDistrib latent observation selectedLaw =ᵐ[selectedLaw.map observation]
      condDistrib latent observation law := by
  intro selectedLaw
  letI : IsProbabilityMeasure selectedLaw :=
    lg21NormalizedRestriction_isProbability law (observation ⁻¹' selected)
      (ne_of_gt hpositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
  let posterior : Kernel Observation Latent := condDistrib latent observation law
  letI : IsProbabilityMeasure (law.map observation) :=
    Measure.isProbabilityMeasure_map hobservation.aemeasurable
  have hrawFactor :
      law.map (fun omega => (observation omega, latent omega)) =
        law.map observation ⊗ₘ posterior := by
    simpa [posterior] using
      (compProd_map_condDistrib (μ := law) (X := observation)
        hlatent.aemeasurable).symm
  have hselectedObservation :
      selectedLaw.map observation =
        lg21NormalizedRestriction (law.map observation) selected := by
    change (lg21NormalizedRestriction law (observation ⁻¹' selected)).map
        observation = _
    exact lg21_normalizedRestriction_map_preimage law observation hobservation
      selected hselected
  have hselectedFactor :
      selectedLaw.map (fun omega => (observation omega, latent omega)) =
        selectedLaw.map observation ⊗ₘ posterior := by
    calc
      selectedLaw.map (fun omega => (observation omega, latent omega)) =
          lg21NormalizedRestriction
            (law.map (fun omega => (observation omega, latent omega)))
            (selected ×ˢ Set.univ) := by
            change (lg21NormalizedRestriction law (observation ⁻¹' selected)).map
                (fun omega => (observation omega, latent omega)) = _
            exact lg21_selectedObservation_normalizedRestriction_map_pair
              law observation latent hobservation hlatent selected hselected
      _ = lg21NormalizedRestriction (law.map observation ⊗ₘ posterior)
          (selected ×ˢ Set.univ) := by rw [hrawFactor]
      _ = lg21NormalizedRestriction (law.map observation) selected ⊗ₘ posterior :=
        lg21_normalizedRestriction_compProd_left
          (law.map observation) posterior selected hselected
      _ = selectedLaw.map observation ⊗ₘ posterior := by
        rw [hselectedObservation]
  exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    hobservation hlatent hselectedFactor

/-- A conditional-mean PBO remains valid after restricting the population to
a positive event determined by the same public observation.  The conclusion
uses the conditional distribution of the restricted law, so it does not
silently reuse a global posterior on a locally selected population. -/
theorem lg21_selectedObservation_condDistribMean_eq_raw_ae
    {Omega Observation : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Observation]
    (law : Measure Omega) [IsProbabilityMeasure law] [IsFiniteMeasure law]
    (observation : Omega -> Observation) (latent : Omega -> ℝ)
    (payoff : Observation -> ℝ)
    (hobservation : Measurable observation) (hlatent : Measurable latent)
    (hPBO : ∀ᵐ publicObservation ∂law.map observation,
      payoff publicObservation =
        ∫ latentSkill, latentSkill ∂
          condDistrib latent observation law publicObservation)
    (selected : Set Observation) (hselected : MeasurableSet selected)
    (hpositive : 0 < law (observation ⁻¹' selected)) :
    let selectedLaw := lg21NormalizedRestriction law (observation ⁻¹' selected)
    letI : IsProbabilityMeasure selectedLaw :=
      lg21NormalizedRestriction_isProbability law (observation ⁻¹' selected)
        (ne_of_gt hpositive) (measure_ne_top _ _)
    letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
    ∀ᵐ publicObservation ∂selectedLaw.map observation,
      payoff publicObservation =
        ∫ latentSkill, latentSkill ∂
          condDistrib latent observation selectedLaw publicObservation := by
  intro selectedLaw
  letI : IsProbabilityMeasure selectedLaw :=
    lg21NormalizedRestriction_isProbability law (observation ⁻¹' selected)
      (ne_of_gt hpositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
  have hselectedMap : selectedLaw.map observation =
      lg21NormalizedRestriction (law.map observation) selected := by
    change (lg21NormalizedRestriction law (observation ⁻¹' selected)).map
        observation = _
    exact lg21_normalizedRestriction_map_preimage law observation hobservation
      selected hselected
  have hPBOOnSelected : ∀ᵐ publicObservation ∂
      lg21NormalizedRestriction (law.map observation) selected,
      payoff publicObservation =
        ∫ latentSkill, latentSkill ∂
          condDistrib latent observation law publicObservation := by
    unfold lg21NormalizedRestriction
    refine Measure.ae_smul_measure ?_ _
    exact (ae_restrict_iff' hselected).2
      (hPBO.mono fun _ hPBO _ => hPBO)
  have hconditional : condDistrib latent observation selectedLaw =ᵐ[
      selectedLaw.map observation] condDistrib latent observation law := by
    simpa only using
      (lg21_selectedObservation_condDistrib_latent_eq_raw_ae
        law observation latent hobservation hlatent selected hselected hpositive)
  rw [hselectedMap] at hconditional ⊢
  filter_upwards [hPBOOnSelected, hconditional] with publicObservation hPBO hconditional
  rw [hconditional]
  exact hPBO

/-- Localizing a population on a public-base region commutes with first
forming any measurable action branch and recording an observation that retains
that base.  This is an equality of action laws, before any posterior is
chosen. -/
theorem lg21_normalizedLocalBaseActionLaw_eq_normalizedGlobalActionLaw
    {Omega Base Record : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Base] [MeasurableSpace Record]
    (law : Measure Omega) [IsFiniteMeasure law]
    (base : Omega -> Base) (record : Omega -> Record)
    (recordBase : Record -> Base)
    (hbase : Measurable base) (hrecord : Measurable record)
    (hrecordBase : Measurable recordBase)
    (hbaseRecord : ∀ omega, recordBase (record omega) = base omega)
    (region : Set Base) (hregion : MeasurableSet region)
    (actionEvent : Set Omega) (hactionEvent : MeasurableSet actionEvent) :
    let localLaw := lg21NormalizedRestriction law (base ⁻¹' region)
    let globalActionLaw := (lg21NormalizedRestriction law actionEvent).map record
    let localActionLaw := (lg21NormalizedRestriction localLaw actionEvent).map record
    localActionLaw =
      lg21NormalizedRestriction globalActionLaw (recordBase ⁻¹' region) := by
  intro localLaw globalActionLaw localActionLaw
  have hbaseEvent : MeasurableSet (base ⁻¹' region) := hregion.preimage hbase
  have hrecordRegion : MeasurableSet (recordBase ⁻¹' region) :=
    hregion.preimage hrecordBase
  have hpreimage : record ⁻¹' (recordBase ⁻¹' region) = base ⁻¹' region := by
    ext omega
    simp only [Set.mem_preimage]
    rw [hbaseRecord]
  have hlocalAction :
      lg21NormalizedRestriction localLaw actionEvent =
        lg21NormalizedRestriction law (base ⁻¹' region ∩ actionEvent) := by
    dsimp [localLaw]
    simpa only [lg21NormalizedRestriction, ProbabilityTheory.cond] using
      (cond_cond_eq_cond_inter hbaseEvent hactionEvent law)
  calc
    localActionLaw =
        (lg21NormalizedRestriction law (base ⁻¹' region ∩ actionEvent)).map
          record := by
      change (lg21NormalizedRestriction localLaw actionEvent).map record = _
      rw [hlocalAction]
    _ = (lg21NormalizedRestriction law (actionEvent ∩ base ⁻¹' region)).map
          record := by rw [Set.inter_comm]
    _ = (lg21NormalizedRestriction
          (lg21NormalizedRestriction law actionEvent) (base ⁻¹' region)).map
          record := by
      congr 1
      symm
      simpa only [lg21NormalizedRestriction, ProbabilityTheory.cond] using
        (cond_cond_eq_cond_inter hactionEvent hbaseEvent law)
    _ = lg21NormalizedRestriction
          ((lg21NormalizedRestriction law actionEvent).map record)
          (recordBase ⁻¹' region) := by
      rw [← hpreimage]
      exact lg21_normalizedRestriction_map_preimage
        (lg21NormalizedRestriction law actionEvent) record hrecord
        (recordBase ⁻¹' region) hrecordRegion

end

end LG21TestOptionalPolicies
