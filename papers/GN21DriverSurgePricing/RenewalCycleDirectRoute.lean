import GN21DriverSurgePricing.RawMarkedStoppedPathBridge

/-!
# Direct raw-cycle routes for GN21 Lemmas 1 and 3

The source-facing stochastic routes in this module start with literal raw
clock/mark product seeds.  They do not accept an IID-cycle record: the raw
product construction proves the independence and identical-law obligations.
The remaining premises are intentionally the semantic, integrability, and
mean-calculation obligations for the actual source cycle observables.
-/

namespace GN21DriverSurgePricing

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

/--
Direct Lemma 3 route from literal raw GN21 cycle seeds.  The two supplied
functions must be the actual larger-cycle state-time observables; their
measurability, integrability, and source mean calculations remain explicit.
All IID fields used by the strong law are derived from the raw product seed
path rather than supplied by a caller.
-/
theorem paper_lemma3_stochastic_time_fraction_formula_of_raw_cycle_observables
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    (sigmaI sigmaJ : TripPolicy)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (hsigmaI_measurable : MeasurableSet sigmaI)
    (hsigmaJ_measurable : MeasurableSet sigmaJ)
    (hsigmaI_subset : Set.Subset sigmaI acceptAllPolicy)
    (hsigmaJ_subset : Set.Subset sigmaJ acceptAllPolicy)
    (hmassI : 0 < singleStateTripMass muI sigmaI)
    (hmassJ : 0 < singleStateTripMass muJ sigmaJ)
    (stateTimeI stateTimeJ : GN21RawCycleSeed -> Real)
    (hstateTimeI_measurable : Measurable stateTimeI)
    (hstateTimeJ_measurable : Measurable stateTimeJ)
    (hstateTimeI_integrable : Integrable stateTimeI
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI))
    (hstateTimeJ_integrable : Integrable stateTimeJ
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI))
    (hstateTimeI_mean :
      (∫ seed, stateTimeI seed
        ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
        gn21ExpectedStateTimeInRenewalCycle arrivalI
          (singleStateTripMass muI sigmaI) switchIJ
          (gn21StateCycleTime muI arrivalI sigmaI)
          (gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI))
    (hstateTimeJ_mean :
      (∫ seed, stateTimeJ seed
        ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
        gn21ExpectedStateTimeInRenewalCycle arrivalJ
          (singleStateTripMass muJ sigmaJ) switchJI
          (gn21StateCycleTime muJ arrivalJ sigmaJ)
          (gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ)) :
    ∀ᵐ omega ∂gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI,
      Tendsto
        (fun n : Nat =>
          (∑ k ∈ Finset.range n, stateTimeI (gn21RawCycleSeedAt k omega)) /
            ((∑ k ∈ Finset.range n, stateTimeI (gn21RawCycleSeedAt k omega)) +
              (∑ k ∈ Finset.range n, stateTimeJ (gn21RawCycleSeedAt k omega))))
        atTop
        (nhds
          (gn21MeasuredTimeFraction muI muJ arrivalI arrivalJ switchIJ
            switchJI sigmaI sigmaJ)) := by
  let C : GN21TimeFractionIIDCycleModel
      (gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
      muI muJ arrivalI arrivalJ switchIJ switchJI sigmaI sigmaJ :=
    gn21TimeFractionIIDCycleModel_of_rawCycleObservables muI muJ
      arrivalI arrivalJ switchIJ switchJI sigmaI sigmaJ harrivalI harrivalJ
      hswitchIJ hswitchJI hsigmaI_measurable hsigmaJ_measurable hsigmaI_subset
      hsigmaJ_subset hmassI hmassJ stateTimeI stateTimeJ hstateTimeI_measurable
      hstateTimeJ_measurable hstateTimeI_integrable hstateTimeJ_integrable
      hstateTimeI_mean hstateTimeJ_mean
  simpa [C] using
    (paper_lemma3_stochastic_time_fraction_formula_of_iid_cycles C)

/--
Direct Lemma 1 route from literal raw GN21 cycle seeds.  As in the Lemma 3
route, the four observables are required to implement the actual larger-cycle
semantics and satisfy the displayed source mean identities.  No IID-cycle
certificate is accepted from the caller: all four IID families are derived
from independent raw seed coordinates.
-/
theorem paper_lemma1_stochastic_dynamic_reward_decomposition_of_raw_cycle_observables
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    (wI wJ : PricingFunction) (sigmaI sigmaJ : TripPolicy)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (hsigmaI_measurable : MeasurableSet sigmaI)
    (hsigmaJ_measurable : MeasurableSet sigmaJ)
    (hsigmaI_subset : Set.Subset sigmaI acceptAllPolicy)
    (hsigmaJ_subset : Set.Subset sigmaJ acceptAllPolicy)
    (hmassI : 0 < singleStateTripMass muI sigmaI)
    (hmassJ : 0 < singleStateTripMass muJ sigmaJ)
    (stateTimeI stateTimeJ stateEarningI stateEarningJ : GN21RawCycleSeed -> Real)
    (hstateTimeI_measurable : Measurable stateTimeI)
    (hstateTimeJ_measurable : Measurable stateTimeJ)
    (hstateEarningI_measurable : Measurable stateEarningI)
    (hstateEarningJ_measurable : Measurable stateEarningJ)
    (hstateTimeI_integrable : Integrable stateTimeI
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI))
    (hstateTimeJ_integrable : Integrable stateTimeJ
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI))
    (hstateEarningI_integrable : Integrable stateEarningI
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI))
    (hstateEarningJ_integrable : Integrable stateEarningJ
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI))
    (hstateTimeI_mean :
      (∫ seed, stateTimeI seed
        ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
        gn21ExpectedStateTimeInRenewalCycle arrivalI
          (singleStateTripMass muI sigmaI) switchIJ
          (gn21StateCycleTime muI arrivalI sigmaI)
          (gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI))
    (hstateTimeJ_mean :
      (∫ seed, stateTimeJ seed
        ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
        gn21ExpectedStateTimeInRenewalCycle arrivalJ
          (singleStateTripMass muJ sigmaJ) switchJI
          (gn21StateCycleTime muJ arrivalJ sigmaJ)
          (gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ))
    (hstateEarningI_mean :
      (∫ seed, stateEarningI seed
        ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
        gn21ExpectedStateEarningInRenewalCycle arrivalI
          (singleStateTripMass muI sigmaI) switchIJ
          (gn21StateMeanEarning muI wI sigmaI)
          (gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI))
    (hstateEarningJ_mean :
      (∫ seed, stateEarningJ seed
        ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
        gn21ExpectedStateEarningInRenewalCycle arrivalJ
          (singleStateTripMass muJ sigmaJ) switchJI
          (gn21StateMeanEarning muJ wJ sigmaJ)
          (gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ)) :
    ∀ᵐ omega ∂gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI,
      Tendsto
        (fun n : Nat =>
          ((∑ k ∈ Finset.range n, stateEarningI (gn21RawCycleSeedAt k omega)) +
              (∑ k ∈ Finset.range n, stateEarningJ (gn21RawCycleSeedAt k omega))) /
            ((∑ k ∈ Finset.range n, stateTimeI (gn21RawCycleSeedAt k omega)) +
              (∑ k ∈ Finset.range n, stateTimeJ (gn21RawCycleSeedAt k omega))))
        atTop
        (nhds
          (gn21MeasuredDynamicReward muI muJ arrivalI arrivalJ switchIJ
            switchJI wI wJ sigmaI sigmaJ)) := by
  let C : GN21DynamicIIDCycleModel
      (gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
      muI muJ arrivalI arrivalJ switchIJ switchJI wI wJ sigmaI sigmaJ :=
    gn21DynamicIIDCycleModel_of_rawCycleObservables muI muJ
      arrivalI arrivalJ switchIJ switchJI wI wJ sigmaI sigmaJ harrivalI harrivalJ
      hswitchIJ hswitchJI hsigmaI_measurable hsigmaJ_measurable hsigmaI_subset
      hsigmaJ_subset hmassI hmassJ stateTimeI stateTimeJ stateEarningI stateEarningJ
      hstateTimeI_measurable hstateTimeJ_measurable hstateEarningI_measurable
      hstateEarningJ_measurable hstateTimeI_integrable hstateTimeJ_integrable
      hstateEarningI_integrable hstateEarningJ_integrable hstateTimeI_mean
      hstateTimeJ_mean hstateEarningI_mean hstateEarningJ_mean
  simpa [C] using
    (paper_lemma1_stochastic_dynamic_reward_decomposition_of_iid_cycles C)

end

end GN21DriverSurgePricing
