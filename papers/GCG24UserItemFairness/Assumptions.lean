import GCG24UserItemFairness.MainTheorems

/-!
# Paper Assumptions: GCG24 User-Item Fairness

This file records source model assumptions and paper-statement conditions used
by the compact human-facing interface. These are not proof certificates.

The paper says that users come in `K` types. In the paper-facing Proposition 2
and Theorems 3--4 wrappers, this is encoded semantically as surjectivity of the
user-to-type map: every declared type has at least one actual user. Lean then
chooses representatives internally from that premise.
-/

namespace GCG24UserItemFairness

open scoped BigOperators

noncomputable section

/--
The source model uses strictly positive recommendation utilities. This covers
Proposition 2's symmetric model and Theorem 3's two opposing-type models.
-/
-- audit-premise: hPos : S.model.Positive
-- audit-premise: hPos' : S'.model.Positive
abbrev assumption_positive_recommendation_utilities {m n : ℕ}
    (W : RecommendationModel m n) : Prop :=
  W.Positive

/--
Proposition 2 defines types by utility rows: users with identical utility
vectors are the same type. `SymmetricData.agreeWithinTypes` records the reverse
implication, so this premise makes the partition exact rather than allowing an
arbitrary refinement of equal-utility users.
-/
-- audit-premise: hRowsDetermineTypes : S.types.UtilityRowsDetermineTypes S.model
abbrev assumption_proposition2_utility_rows_determine_types {m n K : ℕ}
    (S : RecommendationModel.SymmetricData m n K) : Prop :=
  S.types.UtilityRowsDetermineTypes S.model

/--
Theorem 3 compares two instances of the opposing two-type source model with
the same positive, strictly decreasing value vector.
-/
-- audit-premise: hTypes : Function.Surjective S.types.toType
-- audit-premise: hTypes' : Function.Surjective S'.types.toType
abbrev assumption_theorem3_opposing_type_model {m n : ℕ}
    (S S' : RecommendationModel.SymmetricData m n 2)
    (hTypes : Function.Surjective S.types.toType)
    (hTypes' : Function.Surjective S'.types.toType)
    (alpha alpha' : ℝ) (v : Item n → ℝ) : Prop :=
  (S.canonicalReductionOfSurjective hTypes).reduced =
      OpposingTypes.twoTypeReducedModel alpha v ∧
    (S'.canonicalReductionOfSurjective hTypes').reduced =
      OpposingTypes.twoTypeReducedModel alpha' v ∧
    (∀ j : Item n, 0 < v j) ∧
    OpposingTypes.StrictlyDecreasingByIndex v

/--
Theorem 3 first-half domain: `alpha` moves toward the balanced population from
below.
-/
-- audit-premise: halpha0 : 0 < alpha
-- audit-premise: halpha1 : alpha < 1
-- audit-premise: halpha0' : 0 < alpha'
-- audit-premise: halpha1' : alpha' < 1
-- audit-premise: halpha_le : alpha ≤ alpha'
-- audit-premise: halpha_half : alpha ≤ 1 / 2
-- audit-premise: halpha_half' : alpha' ≤ 1 / 2
abbrev assumption_theorem3_first_half_alpha_domain
    (alpha alpha' : ℝ) : Prop :=
  0 < alpha ∧ alpha < 1 ∧
    0 < alpha' ∧ alpha' < 1 ∧
    alpha ≤ alpha' ∧ alpha ≤ 1 / 2 ∧ alpha' ≤ 1 / 2

/--
Theorem 3 second-half domain: `alpha` moves away from the balanced population
above `1 / 2`.
-/
-- audit-premise: halpha0 : 0 < alpha
-- audit-premise: halpha1 : alpha < 1
-- audit-premise: halpha0' : 0 < alpha'
-- audit-premise: halpha1' : alpha' < 1
-- audit-premise: halpha_le : alpha ≤ alpha'
-- audit-premise: halpha_half : 1 / 2 ≤ alpha
-- audit-premise: halpha_half' : 1 / 2 ≤ alpha'
abbrev assumption_theorem3_second_half_alpha_domain
    (alpha alpha' : ℝ) : Prop :=
  0 < alpha ∧ alpha < 1 ∧
    0 < alpha' ∧ alpha' < 1 ∧
    alpha ≤ alpha' ∧ 1 / 2 ≤ alpha ∧ 1 / 2 ≤ alpha'

/--
The Theorem 4 construction uses at least three items.
-/
-- audit-premise: hn : 2 < n
abbrev assumption_theorem4_at_least_three_items (n : ℕ) : Prop :=
  2 < n

/--
The Theorem 4 true model is the displayed two-type symmetric source model.
-/
-- audit-premise: htrue : E.trueModel = Strue.model
abbrev assumption_theorem4_true_model_reduction {m n : ℕ}
    (E : EstimatedRecommendationModel m n)
    (Strue : RecommendationModel.SymmetricData m n 2) : Prop :=
  E.trueModel = Strue.model

/--
The Theorem 4 estimated model is the displayed three-type symmetric source
model.
-/
-- audit-premise: hestimated : E.estimatedModel = Sest.model
abbrev assumption_theorem4_estimated_model_reduction {m n : ℕ}
    (E : EstimatedRecommendationModel m n)
    (Sest : RecommendationModel.SymmetricData m n 3) : Prop :=
  E.estimatedModel = Sest.model

/--
Theorem 4 fixes the true two-type model and the three-type estimated model
through the displayed reduced matrices.
-/
-- audit-premise: hredTrue : (Strue.canonicalReduction repsTrue).reduced = OpposingTypes.twoTypeReducedModel (1 / 2 : ℝ) (OpposingTypes.theorem4SmallValueVector (n := n) eps)
-- audit-premise: hredEst : (Sest.canonicalReduction repsEst).reduced = OpposingTypes.theorem4EstimatedReducedModel beta (OpposingTypes.theorem4SmallValueVector (n := n) eps)
-- audit-premise: hTypesTrue : Function.Surjective Strue.types.toType
-- audit-premise: hTypesEst : Function.Surjective Sest.types.toType
abbrev assumption_theorem4_displayed_reduced_models {m n : ℕ}
    (Strue : RecommendationModel.SymmetricData m n 2)
    (Sest : RecommendationModel.SymmetricData m n 3)
    (hTypesTrue : Function.Surjective Strue.types.toType)
    (hTypesEst : Function.Surjective Sest.types.toType)
    (beta eps : ℝ) : Prop :=
  (Strue.canonicalReductionOfSurjective hTypesTrue).reduced =
      OpposingTypes.twoTypeReducedModel (1 / 2 : ℝ)
        (OpposingTypes.theorem4SmallValueVector (n := n) eps) ∧
    (Sest.canonicalReductionOfSurjective hTypesEst).reduced =
      OpposingTypes.theorem4EstimatedReducedModel beta
        (OpposingTypes.theorem4SmallValueVector (n := n) eps)

/--
Theorem 4's cold-start row is the estimated third type, whose true type is one
of the two opposing source rows.
-/
-- audit-premise: hknown0 : ∀ u : User m, Sest.types.toType u = 0 → Strue.types.toType u = 0
-- audit-premise: hknown1 : ∀ u : User m, Sest.types.toType u = 1 → Strue.types.toType u = 1
-- audit-premise: htrueType : Strue.types.toType u = 0
-- audit-premise: htrueType : Strue.types.toType u = 1
-- audit-premise: hestimatedType : Sest.types.toType u = 2
abbrev assumption_theorem4_cold_start_type_wiring {m n : ℕ}
    (Strue : RecommendationModel.SymmetricData m n 2)
    (Sest : RecommendationModel.SymmetricData m n 3)
    (u : User m) : Prop :=
  (∀ u : User m, Sest.types.toType u = 0 → Strue.types.toType u = 0) ∧
    (∀ u : User m, Sest.types.toType u = 1 → Strue.types.toType u = 1) ∧
    (Strue.types.toType u = 0 ∨ Strue.types.toType u = 1) ∧
    Sest.types.toType u = 2

/--
Theorem 4 parameter domain for the arbitrary-large misestimation conclusion.
-/
-- audit-premise: heps : 0 < eps
-- audit-premise: hbeta : (n : ℝ)⁻¹ < beta
-- audit-premise: hbeta_half : beta < 1 / 2
abbrev assumption_theorem4_parameter_domain
    (n : ℕ) (beta eps : ℝ) : Prop :=
  0 < eps ∧ (n : ℝ)⁻¹ < beta ∧ beta < 1 / 2

/--
The universal first bullet of Theorem 4 ranges over the positive, strictly
decreasing value vectors fixed in the preceding opposing-preferences model.
-/
-- audit-premise: hpos : ∀ j : Item n, 0 < v j
-- audit-premise: hdec : OpposingTypes.StrictlyDecreasingByIndex v
abbrev assumption_theorem4_universal_value_vector {n : ℕ}
    (v : Item n → ℝ) : Prop :=
  (∀ j : Item n, 0 < v j) ∧ OpposingTypes.StrictlyDecreasingByIndex v

end

end GCG24UserItemFairness
