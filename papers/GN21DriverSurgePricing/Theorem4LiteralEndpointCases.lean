import GN21DriverSurgePricing.Theorem4EndpointDerivativeBridge
import GN21DriverSurgePricing.Theorem4FixedMarginal

/-!
# Literal endpoint cases for GN21 Theorem 4

This module composes the source's state-local positive-endpoint branch with
the existing direct affine branches. It deliberately does not turn a positive
endpoint derivative into pointwise marginal-response positivity.
-/

open MeasureTheory
open scoped ENNReal Topology symmDiff

namespace GN21DriverSurgePricing

noncomputable section

/-- The non-surge half of the printed Theorem 4 price table, retaining the
third branch as the literal derivative condition on actual state-0 components.
-/
def gn21Theorem4NonsurgeLiteralEndpointPriceCase
    (R : DynamicReward) (w : Fin 2 → PricingFunction)
    (shape : Fin 2 → Lemma5DerivativeShape) : Prop :=
  (∃ m a : ℝ,
    0 ≤ a ∧ w 0 = affinePricing m a ∧
      shape 0 = .strictlyDecreasing) ∨
  (∃ m a : ℝ,
    0 < a ∧ w 0 = affinePricing m (-a) ∧
      shape 0 = .strictlyQuasiConcave) ∨
  (gn21SourceUpperEndpointDerivativePositiveAt R 0 ∧
    shape 0 = .positive)

/-- The surge half of the printed Theorem 4 price table, retaining the third
branch as the literal derivative condition on actual state-1 components. -/
def gn21Theorem4SurgeLiteralEndpointPriceCase
    (R : DynamicReward) (w : Fin 2 → PricingFunction)
    (shape : Fin 2 → Lemma5DerivativeShape) : Prop :=
  (∃ m a : ℝ,
    0 ≤ a ∧ w 1 = affinePricing m (-a) ∧
      shape 1 = .strictlyIncreasing) ∨
  (∃ m a : ℝ,
    0 < a ∧ w 1 = affinePricing m a ∧
      shape 1 = .strictlyQuasiConvex) ∨
  (gn21SourceUpperEndpointDerivativePositiveAt R 1 ∧
    shape 1 = .positive)

/-- The source Theorem 4 replacement order needs only one canonical
replacement for each state after the surge-rate step. The replacements are
statewise: they may come from an affine marginal calculation or from the
literal endpoint-positive argument. -/
theorem gn21_exists_open_canonical_dominating_policy_of_statewise_replacements
    (mu : Fin 2 → Measure TripLength)
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    (arrival : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (shape : Fin 2 → Lemma5DerivativeShape)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (hsurge : gn21SourceSurgeStateDominance mu arrival w)
    (hleft_replace :
      ∀ rho : Fin 2 → TripPolicy,
        dynamicFeasibleOpenPolicy rho →
          gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (rho 0) <
            gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) (rho 1) →
            ∃ endpoints : GN21Lemma5EndpointVector (gn21Lemma5CanonicalExtra (shape 0)),
              endpoints ∈ gn21Lemma5CanonicalEndpointDomain (shape 0) ∧
                gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w rho ≤
                  gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
                    (Function.update rho 0 (gn21EndpointVectorPolicy endpoints)))
    (hright_replace :
      ∀ rho : Fin 2 → TripPolicy,
        dynamicFeasibleOpenPolicy rho →
          gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (rho 0) <
            gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) (rho 1) →
            ∃ endpoints : GN21Lemma5EndpointVector (gn21Lemma5CanonicalExtra (shape 1)),
              endpoints ∈ gn21Lemma5CanonicalEndpointDomain (shape 1) ∧
                gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w rho ≤
                  gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
                    (Function.update rho 1 (gn21EndpointVectorPolicy endpoints)))
    (rho : Fin 2 → TripPolicy)
    (hrho : dynamicFeasibleOpenPolicy rho) :
    ∃ endpoints : GN21Lemma5CanonicalPairEndpointVector shape,
      endpoints ∈ gn21Lemma5CanonicalPairEndpointDomain shape ∧
        gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w rho ≤
          gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
            (gn21Lemma5CanonicalPairPolicy shape endpoints) := by
  let R : DynamicReward :=
    gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
  let rate0 : (Fin 2 → TripPolicy) → ℝ := fun sigma =>
    gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (sigma 0)
  let rate1 : (Fin 2 → TripPolicy) → ℝ := fun sigma =>
    gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) (sigma 1)
  have ensure_rate :
      ∀ sigma : Fin 2 → TripPolicy,
        dynamicFeasibleOpenPolicy sigma →
          ∃ sigma' : Fin 2 → TripPolicy,
            dynamicFeasibleOpenPolicy sigma' ∧
              R sigma ≤ R sigma' ∧
                rate0 sigma' < rate1 sigma' ∧
                  sigma' 0 = sigma 0 := by
    intro sigma hsigma
    by_cases hrate_le : rate1 sigma ≤ rate0 sigma
    · rcases gn21SourceSurgeStateDominance_exists_right_improvement_of_rate_le
          mu arrival switch12 switch21 w harrival0_pos harrival1_pos
          hswitch12_pos hswitch21_pos hsurge hsigma
          (by simpa [rate0, rate1] using hrate_le) with
        ⟨sigma2, hsigma2_subset, hsigma2_open, hdominates, himproves⟩
      let sigma' : Fin 2 → TripPolicy := Function.update sigma 1 sigma2
      have hsigma'_open : dynamicFeasibleOpenPolicy sigma' := by
        dsimp [sigma']
        exact dynamicFeasibleOpenPolicy_update hsigma 1 sigma2 hsigma2_subset hsigma2_open
      have himproves_R : R sigma < R sigma' := by
        simpa [R, sigma'] using himproves
      have hrate_lt : rate0 sigma' < rate1 sigma' := by
        have h := hdominates (sigma' 0) (hsigma'_open 0).1 (hsigma'_open 0).2
        simpa [rate0, rate1, sigma'] using h
      refine ⟨sigma', hsigma'_open, le_of_lt himproves_R, hrate_lt, ?_⟩
      simp [sigma']
    · exact ⟨sigma, hsigma, le_rfl, lt_of_not_ge hrate_le, rfl⟩
  rcases ensure_rate rho hrho with
    ⟨rhoA, hrhoA_open, hrho_le_A, hrateA, _⟩
  rcases hleft_replace rhoA hrhoA_open (by simpa [rate0, rate1] using hrateA) with
    ⟨leftEndpoints, hleft_domain, hA_le_B⟩
  let leftCandidate : TripPolicy := gn21EndpointVectorPolicy leftEndpoints
  have hleft_subset : leftCandidate ⊆ acceptAllPolicy := by
    dsimp [leftCandidate]
    exact gn21EndpointVectorPolicy_subset_acceptAll leftEndpoints
  have hleft_open : IsOpen leftCandidate := by
    dsimp [leftCandidate]
    exact gn21EndpointVectorPolicy_open leftEndpoints
  let rhoB : Fin 2 → TripPolicy := Function.update rhoA 0 leftCandidate
  have hrhoB_open : dynamicFeasibleOpenPolicy rhoB := by
    dsimp [rhoB]
    exact dynamicFeasibleOpenPolicy_update hrhoA_open 0 leftCandidate
      hleft_subset hleft_open
  rcases ensure_rate rhoB hrhoB_open with
    ⟨rhoC, hrhoC_open, hB_le_C, hrateC, hrhoC_zero⟩
  have hleft_C : rhoC 0 = gn21EndpointVectorPolicy leftEndpoints := by
    rw [hrhoC_zero]
    rfl
  rcases hright_replace rhoC hrhoC_open (by simpa [rate0, rate1] using hrateC) with
    ⟨rightEndpoints, hright_domain, hC_le_tau⟩
  let rightCandidate : TripPolicy := gn21EndpointVectorPolicy rightEndpoints
  let tau : Fin 2 → TripPolicy := Function.update rhoC 1 rightCandidate
  let endpoints : GN21Lemma5CanonicalPairEndpointVector shape :=
    (leftEndpoints, rightEndpoints)
  have hendpoints_domain : endpoints ∈ gn21Lemma5CanonicalPairEndpointDomain shape :=
    ⟨hleft_domain, hright_domain⟩
  have hendpoints_policy :
      gn21Lemma5CanonicalPairPolicy shape endpoints = tau := by
    funext i
    fin_cases i
    · simpa [endpoints, gn21Lemma5CanonicalPairPolicy, tau] using hleft_C.symm
    · simp [endpoints, gn21Lemma5CanonicalPairPolicy, tau, rightCandidate]
  refine ⟨endpoints, hendpoints_domain, ?_⟩
  rw [hendpoints_policy]
  exact hrho_le_A.trans (hA_le_B.trans (hB_le_C.trans hC_le_tau))

/-- Source-faithful compact attainment for the printed Theorem 4 price table.

The affine rows use their existing fixed-current marginal calculations.  In a
positive row, the replacement is instead the literal upper-endpoint argument
from Lemma 5, applied only in that state.  The source continuity-in-policy
condition is explicit below; continuity on finite endpoint vectors is derived
from the actual integrable aggregate model. -/
theorem exists_gn21AggregateDynamicOpenOptimal_of_literal_endpoint_price_cases
    (mu : Fin 2 → Measure TripLength)
    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    [(mu 0).InnerRegularCompactLTTop] [(mu 1).InnerRegularCompactLTTop]
    (arrival : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (shape : Fin 2 → Lemma5DerivativeShape)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (hw0_measurable : Measurable (w 0)) (hw1_measurable : Measurable (w 1))
    (htime0 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 0))
    (htime1 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1))
    (hw0 : IntegrableOn (w 0) acceptAllPolicy (mu 0))
    (hw1 : IntegrableOn (w 1) acceptAllPolicy (mu 1))
    (hsurge : gn21SourceSurgeStateDominance mu arrival w)
    (hnonsurge_price_case :
      gn21Theorem4NonsurgeLiteralEndpointPriceCase
        (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w) w shape)
    (hsurge_price_case :
      gn21Theorem4SurgeLiteralEndpointPriceCase
        (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w) w shape)
    (hcontinuous :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (tau : TripPolicy),
            GN21SymmDiffContinuousAt (mu i)
              (fun policy =>
                gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
                  (Function.update rho i policy)) tau) :
    ∃ rho : Fin 2 → TripPolicy,
      dynamicOpenOptimal
        (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w) rho := by
  let R : DynamicReward :=
    gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
  have hfinite : ∀ i : Fin 2, IsFiniteMeasure (mu i) := by
    intro i
    exact Fin.cases (inferInstance : IsFiniteMeasure (mu 0))
      (fun j =>
        Fin.cases (inferInstance : IsFiniteMeasure (mu 1))
          (fun k => Fin.elim0 k) j) i
  have hinner : ∀ i : Fin 2, (mu i).InnerRegularCompactLTTop := by
    intro i
    fin_cases i <;> infer_instance
  have hatomless : ∀ i : Fin 2, NoAtoms (mu i) := by
    intro i
    exact Fin.cases (inferInstance : NoAtoms (mu 0))
      (fun j =>
        Fin.cases (inferInstance : NoAtoms (mu 1))
          (fun k => Fin.elim0 k) j) i
  have hcontinuous_R :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (tau : TripPolicy),
            GN21SymmDiffContinuousAt (mu i)
              (fun policy => R (Function.update rho i policy)) tau := by
    simpa [R] using hcontinuous
  have hendpoint_continuous_R :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (state : Fin 2) (extra : Nat),
            ContinuousOn
              (fun endpoints : GN21Lemma5EndpointVector extra =>
                R (Function.update rho state (gn21EndpointVectorPolicy endpoints)))
              (gn21Lemma5EndpointDomain .positive extra) := by
    intro rho hrho state extra
    simpa [R] using
      (continuousOn_gn21AggregateDynamicRewardFunctional_update_endpointPolicy
        mu arrival switch12 switch21 w harrival0_pos harrival1_pos
        hswitch12_pos hswitch21_pos htime0 htime1 hw0 hw1 rho hrho state extra)
  have hsum0 : 0 < switch12 + switch21 := add_pos hswitch12_pos hswitch21_pos
  have hsum1 : 0 < switch21 + switch12 := add_pos hswitch21_pos hswitch12_pos
  have hq0 :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switch12 switch21 tau)
        acceptAllPolicy (mu 0) := by
    exact integrableOn_gn21SwitchProb_of_time_integrable
      (mu 0) switch12 switch21 acceptAllPolicy (le_of_lt hswitch12_pos)
      hsum0 (fun _ h => h) measurableSet_acceptAllPolicy htime0
  have hq1 :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switch21 switch12 tau)
        acceptAllPolicy (mu 1) := by
    exact integrableOn_gn21SwitchProb_of_time_integrable
      (mu 1) switch21 switch12 acceptAllPolicy (le_of_lt hswitch21_pos)
      hsum1 (fun _ h => h) measurableSet_acceptAllPolicy htime1
  have hleft_replace :
      ∀ rho : Fin 2 → TripPolicy,
        dynamicFeasibleOpenPolicy rho →
          gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (rho 0) <
            gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) (rho 1) →
            ∃ endpoints : GN21Lemma5EndpointVector (gn21Lemma5CanonicalExtra (shape 0)),
              endpoints ∈ gn21Lemma5CanonicalEndpointDomain (shape 0) ∧
                R rho ≤ R (Function.update rho 0 (gn21EndpointVectorPolicy endpoints)) := by
    intro rho hrho hrate
    rcases hnonsurge_price_case with hcase | hcase | hcase
    · rcases gn21_exists_leftCanonicalEndpoint_of_affine_source_case
          mu arrival switch12 switch21 w shape harrival0_pos harrival1_pos
          hswitch12_pos hswitch21_pos (Or.inl hcase) rho hrho hrate with
        ⟨endpoints, hendpoints, hpolicy⟩
      refine ⟨endpoints, hendpoints, ?_⟩
      rw [hpolicy]
      simpa [R] using
        (gn21AggregateDynamicRewardFunctional_le_update_left_positiveResponse
          mu arrival switch12 switch21 w harrival0_pos harrival1_pos
          hswitch12_pos hswitch21_pos hw0_measurable hq0 hw0 htime0
          hrho.to_measurable)
    · rcases gn21_exists_leftCanonicalEndpoint_of_affine_source_case
          mu arrival switch12 switch21 w shape harrival0_pos harrival1_pos
          hswitch12_pos hswitch21_pos (Or.inr (Or.inl hcase)) rho hrho hrate with
        ⟨endpoints, hendpoints, hpolicy⟩
      refine ⟨endpoints, hendpoints, ?_⟩
      rw [hpolicy]
      simpa [R] using
        (gn21AggregateDynamicRewardFunctional_le_update_left_positiveResponse
          mu arrival switch12 switch21 w harrival0_pos harrival1_pos
          hswitch12_pos hswitch21_pos hw0_measurable hq0 hw0 htime0
          hrho.to_measurable)
    · rcases hcase with ⟨hsource_actual, hshape⟩
      have hsource : gn21SourceUpperEndpointDerivativePositiveAt R 0 := by
        simpa [R] using hsource_actual
      have hform : lemma5SourcePolicyForm (shape 0) acceptAllPolicy := by
        rw [hshape]
        rfl
      rcases exists_canonicalEndpointVector_of_lemma5SourcePolicyForm hform with
        ⟨endpoints, hendpoints, hpolicy⟩
      refine ⟨endpoints, hendpoints, ?_⟩
      rw [hpolicy]
      have hdominance :=
        gn21SourceUpperEndpointDerivativePositive_state_reward_le_acceptAll
          mu hfinite hinner hatomless R 0 hsource hrho hcontinuous_R
          (hendpoint_continuous_R rho hrho 0) (rho 0) (hrho 0).2 (hrho 0).1
      simpa [Function.update_eq_self] using hdominance
  have hright_replace :
      ∀ rho : Fin 2 → TripPolicy,
        dynamicFeasibleOpenPolicy rho →
          gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (rho 0) <
            gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) (rho 1) →
            ∃ endpoints : GN21Lemma5EndpointVector (gn21Lemma5CanonicalExtra (shape 1)),
              endpoints ∈ gn21Lemma5CanonicalEndpointDomain (shape 1) ∧
                R rho ≤ R (Function.update rho 1 (gn21EndpointVectorPolicy endpoints)) := by
    intro rho hrho hrate
    rcases hsurge_price_case with hcase | hcase | hcase
    · rcases gn21_exists_rightCanonicalEndpoint_of_affine_source_case
          mu arrival switch12 switch21 w shape harrival0_pos harrival1_pos
          hswitch12_pos hswitch21_pos (Or.inl hcase) rho hrho hrate with
        ⟨endpoints, hendpoints, hpolicy⟩
      refine ⟨endpoints, hendpoints, ?_⟩
      rw [hpolicy]
      simpa [R] using
        (gn21AggregateDynamicRewardFunctional_le_update_right_positiveResponse
          mu arrival switch12 switch21 w harrival0_pos harrival1_pos
          hswitch12_pos hswitch21_pos hw1_measurable hq1 hw1 htime1
          hrho.to_measurable)
    · rcases gn21_exists_rightCanonicalEndpoint_of_affine_source_case
          mu arrival switch12 switch21 w shape harrival0_pos harrival1_pos
          hswitch12_pos hswitch21_pos (Or.inr (Or.inl hcase)) rho hrho hrate with
        ⟨endpoints, hendpoints, hpolicy⟩
      refine ⟨endpoints, hendpoints, ?_⟩
      rw [hpolicy]
      simpa [R] using
        (gn21AggregateDynamicRewardFunctional_le_update_right_positiveResponse
          mu arrival switch12 switch21 w harrival0_pos harrival1_pos
          hswitch12_pos hswitch21_pos hw1_measurable hq1 hw1 htime1
          hrho.to_measurable)
    · rcases hcase with ⟨hsource_actual, hshape⟩
      have hsource : gn21SourceUpperEndpointDerivativePositiveAt R 1 := by
        simpa [R] using hsource_actual
      have hform : lemma5SourcePolicyForm (shape 1) acceptAllPolicy := by
        rw [hshape]
        rfl
      rcases exists_canonicalEndpointVector_of_lemma5SourcePolicyForm hform with
        ⟨endpoints, hendpoints, hpolicy⟩
      refine ⟨endpoints, hendpoints, ?_⟩
      rw [hpolicy]
      have hdominance :=
        gn21SourceUpperEndpointDerivativePositive_state_reward_le_acceptAll
          mu hfinite hinner hatomless R 1 hsource hrho hcontinuous_R
          (hendpoint_continuous_R rho hrho 1) (rho 1) (hrho 1).2 (hrho 1).1
      simpa [Function.update_eq_self] using hdominance
  have hpair_continuous :
      ContinuousOn
        (fun endpoints : GN21Lemma5CanonicalPairEndpointVector shape =>
          R (gn21Lemma5CanonicalPairPolicy shape endpoints))
        (gn21Lemma5CanonicalPairEndpointDomain shape) := by
    simpa [R] using
      (continuousOn_gn21AggregateDynamicRewardFunctional_canonicalPair
        mu arrival switch12 switch21 w shape harrival0_pos harrival1_pos
        hswitch12_pos hswitch21_pos htime0 htime1 hw0 hw1)
  exact exists_dynamicOpenOptimal_of_weak_canonical_domain_dominance
    R shape hpair_continuous
    (fun rho hrho =>
      gn21_exists_open_canonical_dominating_policy_of_statewise_replacements
        mu arrival switch12 switch21 w shape harrival0_pos harrival1_pos
        hswitch12_pos hswitch21_pos hsurge hleft_replace hright_replace rho hrho)

/-- Every source-open optimum has the literal Theorem 4 forms, modulo the
paper's statewise null-set convention.  A literal positive endpoint row forces
accept-all directly in that state; the other state continues through the
appropriate affine row. -/
theorem gn21_literal_endpoint_sourceFormsAlmostEverywhere_of_dynamicOpenOptimal
    (mu : Fin 2 → Measure TripLength)
    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    (arrival : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (shape : Fin 2 → Lemma5DerivativeShape)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (hw0_measurable : Measurable (w 0)) (hw1_measurable : Measurable (w 1))
    (htime0 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 0))
    (htime1 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1))
    (hw0 : IntegrableOn (w 0) acceptAllPolicy (mu 0))
    (hw1 : IntegrableOn (w 1) acceptAllPolicy (mu 1))
    (hsurge : gn21SourceSurgeStateDominance mu arrival w)
    (hnonsurge_price_case :
      gn21Theorem4NonsurgeLiteralEndpointPriceCase
        (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w) w shape)
    (hsurge_price_case :
      gn21Theorem4SurgeLiteralEndpointPriceCase
        (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w) w shape)
    (hcontinuous :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (tau : TripPolicy),
            GN21SymmDiffContinuousAt (mu i)
              (fun policy =>
                gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
                  (Function.update rho i policy)) tau)
    {rho : Fin 2 → TripPolicy}
    (hrho :
      dynamicOpenOptimal
        (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w) rho) :
    lemma5SourcePolicyFormAlmostEverywhere (mu 0) (shape 0) (rho 0) ∧
      lemma5SourcePolicyFormAlmostEverywhere (mu 1) (shape 1) (rho 1) := by
  let R : DynamicReward :=
    gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
  have hfinite : ∀ i : Fin 2, IsFiniteMeasure (mu i) := by
    intro i
    exact Fin.cases (inferInstance : IsFiniteMeasure (mu 0))
      (fun j =>
        Fin.cases (inferInstance : IsFiniteMeasure (mu 1))
          (fun k => Fin.elim0 k) j) i
  have hatomless : ∀ i : Fin 2, NoAtoms (mu i) := by
    intro i
    exact Fin.cases (inferInstance : NoAtoms (mu 0))
      (fun j =>
        Fin.cases (inferInstance : NoAtoms (mu 1))
          (fun k => Fin.elim0 k) j) i
  have hcontinuous_R :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (tau : TripPolicy),
            GN21SymmDiffContinuousAt (mu i)
              (fun policy => R (Function.update rho i policy)) tau := by
    simpa [R] using hcontinuous
  have hsum0 : 0 < switch12 + switch21 := add_pos hswitch12_pos hswitch21_pos
  have hsum1 : 0 < switch21 + switch12 := add_pos hswitch21_pos hswitch12_pos
  have hq0 :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switch12 switch21 tau)
        acceptAllPolicy (mu 0) := by
    exact integrableOn_gn21SwitchProb_of_time_integrable
      (mu 0) switch12 switch21 acceptAllPolicy (le_of_lt hswitch12_pos)
      hsum0 (fun _ h => h) measurableSet_acceptAllPolicy htime0
  have hq1 :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switch21 switch12 tau)
        acceptAllPolicy (mu 1) := by
    exact integrableOn_gn21SwitchProb_of_time_integrable
      (mu 1) switch21 switch12 acceptAllPolicy (le_of_lt hswitch21_pos)
      hsum1 (fun _ h => h) measurableSet_acceptAllPolicy htime1
  have hrate :
      gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (rho 0) <
        gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) (rho 1) :=
    gn21MeasuredStateRewardRate_lt_of_dynamicOpenOptimal_and_sourceSurgeStateDominance
      mu arrival switch12 switch21 w harrival0_pos harrival1_pos
      hswitch12_pos hswitch21_pos hsurge hrho
  have hleft_ae :
      lemma5SourcePolicyFormAlmostEverywhere (mu 0) (shape 0) (rho 0) := by
    rcases hnonsurge_price_case with hcase | hcase | hcase
    · rcases gn21_left_sourceForm_and_zeroSetNull_of_affine_source_case
          mu arrival switch12 switch21 w shape harrival0_pos harrival1_pos
          hswitch12_pos hswitch21_pos (Or.inl hcase) rho hrho.1 hrate with
        ⟨hform, hzero⟩
      exact gn21Aggregate_left_sourcePolicyFormAlmostEverywhere_of_dynamicOpenOptimal
        mu arrival switch12 switch21 w hrho harrival0_pos harrival1_pos
        hswitch12_pos hswitch21_pos hw0_measurable hq0 hw0 htime0 (shape 0)
        hform hzero
    · rcases gn21_left_sourceForm_and_zeroSetNull_of_affine_source_case
          mu arrival switch12 switch21 w shape harrival0_pos harrival1_pos
          hswitch12_pos hswitch21_pos (Or.inr (Or.inl hcase)) rho hrho.1 hrate with
        ⟨hform, hzero⟩
      exact gn21Aggregate_left_sourcePolicyFormAlmostEverywhere_of_dynamicOpenOptimal
        mu arrival switch12 switch21 w hrho harrival0_pos harrival1_pos
        hswitch12_pos hswitch21_pos hw0_measurable hq0 hw0 htime0 (shape 0)
        hform hzero
    · rcases hcase with ⟨hsource_actual, hshape⟩
      have hsource : gn21SourceUpperEndpointDerivativePositiveAt R 0 := by
        simpa [R] using hsource_actual
      have haccept : rho 0 = acceptAllPolicy :=
        gn21SourceUpperEndpointDerivativePositive_optimal_state_acceptAll_of_symmDiffContinuousAt
          mu hfinite hatomless R 0 hsource hrho hcontinuous_R
      rw [haccept, hshape]
      exact lemma5SourcePolicyFormAlmostEverywhere_of_form (mu 0) (by rfl)
  refine ⟨hleft_ae, ?_⟩
  rcases hsurge_price_case with hcase | hcase | hcase
  · rcases hcase with ⟨m, a, ha_nonneg, hprice, hshape⟩
    rcases gn21MeasuredRight_negativeAffineMarginal_sourceFiniteForm_and_zeroSetNull_of_dynamicOpenOptimal
          mu arrival switch12 switch21 w m a hprice harrival0_pos harrival1_pos
          hswitch12_pos hswitch21_pos ha_nonneg hsurge hq1 hw1 htime1 hrho with
      ⟨hform, hzero⟩
    have hform_shape :
        lemma5SourcePolicyForm (shape 1)
          (lemma5PositiveResponsePolicy
            (gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
              (arrival 0) (arrival 1) switch12 switch21
              (w 0) (w 1) (rho 0) (rho 1))) := by
      rw [hshape]
      exact hform
    exact gn21Aggregate_right_sourcePolicyFormAlmostEverywhere_of_dynamicOpenOptimal
      mu arrival switch12 switch21 w hrho harrival0_pos harrival1_pos
      hswitch12_pos hswitch21_pos hw1_measurable hq1 hw1 htime1 (shape 1)
      hform_shape hzero
  · rcases hcase with ⟨m, a, ha_pos, hprice, hshape⟩
    rcases gn21_right_sourceForm_or_empty_and_zeroSetNull_of_affine_source_case
          mu arrival switch12 switch21 w shape harrival0_pos harrival1_pos
          hswitch12_pos hswitch21_pos
          (Or.inr (Or.inl ⟨m, a, ha_pos, hprice, hshape⟩)) rho hrho.1 hrate with
      ⟨hform_or_empty, hzero⟩
    rcases hform_or_empty with hform | ⟨hincreasing, _⟩
    · exact gn21Aggregate_right_sourcePolicyFormAlmostEverywhere_of_dynamicOpenOptimal
        mu arrival switch12 switch21 w hrho harrival0_pos harrival1_pos
        hswitch12_pos hswitch21_pos hw1_measurable hq1 hw1 htime1 (shape 1)
        hform hzero
    · have hfalse : False := by
        simpa [hshape] using hincreasing
      exact hfalse.elim
  · rcases hcase with ⟨hsource_actual, hshape⟩
    have hsource : gn21SourceUpperEndpointDerivativePositiveAt R 1 := by
      simpa [R] using hsource_actual
    have haccept : rho 1 = acceptAllPolicy :=
      gn21SourceUpperEndpointDerivativePositive_optimal_state_acceptAll_of_symmDiffContinuousAt
        mu hfinite hatomless R 1 hsource hrho hcontinuous_R
    rw [haccept, hshape]
    exact lemma5SourcePolicyFormAlmostEverywhere_of_form (mu 1) (by rfl)

/-- Direct source-facing Theorem 4 assembly with the printed state-local
positive endpoint branches.  The policy-form conclusion is exact for one
attained optimum and is modulo each state's source measure for every optimum,
as in Appendix D. -/
theorem paper_theorem4_literal_endpoint_price_cases_direct
    (mu : Fin 2 → Measure TripLength)
    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    [(mu 0).InnerRegularCompactLTTop] [(mu 1).InnerRegularCompactLTTop]
    (arrival : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (shape : Fin 2 → Lemma5DerivativeShape)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (hw0_measurable : Measurable (w 0)) (hw1_measurable : Measurable (w 1))
    (htime0 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 0))
    (htime1 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1))
    (hw0 : IntegrableOn (w 0) acceptAllPolicy (mu 0))
    (hw1 : IntegrableOn (w 1) acceptAllPolicy (mu 1))
    (hsurge : gn21SourceSurgeStateDominance mu arrival w)
    (hnonsurge_price_case :
      gn21Theorem4NonsurgeLiteralEndpointPriceCase
        (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w) w shape)
    (hsurge_price_case :
      gn21Theorem4SurgeLiteralEndpointPriceCase
        (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w) w shape)
    (hcontinuous :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (tau : TripPolicy),
            GN21SymmDiffContinuousAt (mu i)
              (fun policy =>
                gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
                  (Function.update rho i policy)) tau) :
    (∃ rho : Fin 2 → TripPolicy,
      dynamicOpenOptimal
          (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w) rho ∧
        lemma5SourcePolicyForm (shape 0) (rho 0) ∧
          lemma5SourcePolicyForm (shape 1) (rho 1)) ∧
      ∀ rho : Fin 2 → TripPolicy,
        dynamicOpenOptimal
            (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w) rho →
          lemma5SourcePolicyFormAlmostEverywhere (mu 0) (shape 0) (rho 0) ∧
            lemma5SourcePolicyFormAlmostEverywhere (mu 1) (shape 1) (rho 1) := by
  rcases exists_gn21AggregateDynamicOpenOptimal_of_literal_endpoint_price_cases
      mu arrival switch12 switch21 w shape harrival0_pos harrival1_pos
      hswitch12_pos hswitch21_pos hw0_measurable hw1_measurable htime0 htime1
      hw0 hw1 hsurge hnonsurge_price_case hsurge_price_case hcontinuous with
    ⟨rho, hrho⟩
  have hrho_forms :
      lemma5SourcePolicyFormAlmostEverywhere (mu 0) (shape 0) (rho 0) ∧
        lemma5SourcePolicyFormAlmostEverywhere (mu 1) (shape 1) (rho 1) :=
    gn21_literal_endpoint_sourceFormsAlmostEverywhere_of_dynamicOpenOptimal
      mu arrival switch12 switch21 w shape harrival0_pos harrival1_pos
      hswitch12_pos hswitch21_pos hw0_measurable hw1_measurable htime0 htime1
      hw0 hw1 hsurge hnonsurge_price_case hsurge_price_case hcontinuous hrho
  rcases exists_dynamicOpenOptimal_sourceForms_of_policyFormsAlmostEverywhere
      mu arrival switch12 switch21 w shape hrho hrho_forms.1 hrho_forms.2 with
    ⟨rhoStar, hrhoStar, hform0, hform1⟩
  refine ⟨⟨rhoStar, hrhoStar, hform0, hform1⟩, ?_⟩
  intro rho hrho
  exact gn21_literal_endpoint_sourceFormsAlmostEverywhere_of_dynamicOpenOptimal
    mu arrival switch12 switch21 w shape harrival0_pos harrival1_pos
    hswitch12_pos hswitch21_pos hw0_measurable hw1_measurable htime0 htime1
    hw0 hw1 hsurge hnonsurge_price_case hsurge_price_case hcontinuous hrho

end

end GN21DriverSurgePricing
