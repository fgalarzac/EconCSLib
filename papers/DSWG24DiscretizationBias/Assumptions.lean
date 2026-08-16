import DSWG24DiscretizationBias.MainTheorems

/-!
# Paper Assumptions: DSWG24 Discretization Bias

This file records source theorem conditions used by the paper-facing Lean
interface. The conditions are stated in Theorems 1 and 2 or are standard formal
versions of those statements, such as measurability for the continuous argmax
rule.
-/

namespace DSWG24DiscretizationBias

/-- Theorem 1(i) no-information regime. -/
-- audit-premise: hnoInformation : ∀ x a, q x a = prior μ a
abbrev assumption_theorem1_no_information_case
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (μ : PMF (X × Y)) (q : X → Y → ℝ) : Prop :=
  ∀ x a, q x a = Finite.paperPrior μ a

/-- Theorem 1(i) fixes a plurality/argmax class for the no-information regime. -/
-- audit-premise: hplurality : ∀ a, prior μ a ≤ prior μ z
abbrev assumption_theorem1_plurality_argmax_class
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (μ : PMF (X × Y)) (z : Y) : Prop :=
  ∀ a, Finite.paperPrior μ a ≤ Finite.paperPrior μ z

/-- Theorem 1(ii) perfect-classifier regime. -/
-- audit-premise: htruth : ∀ xy : X × Y, rule xy.1 = xy.2
abbrev assumption_theorem1_perfect_classifier
    (rule : X → Y) : Prop :=
  ∀ xy : X × Y, rule xy.1 = xy.2

/-- The continuous Theorem 1(iii) wrapper requires a measurable argmax rule. -/
-- audit-premise: hrule : Measurable argmaxRule
abbrev assumption_theorem1_argmax_rule_measurable
    [MeasurableSpace X] [MeasurableSpace Y] (argmaxRule : X → Y) : Prop :=
  Measurable argmaxRule

/-- Theorem 1 is stated for calibrated classifiers. -/
-- audit-premise: hcal : calibrated μ q
abbrev assumption_theorem1_calibrated_classifier
    [MeasurableSpace (X × Y)] [DecidableEq Y]
    (μ : MeasureTheory.Measure (X × Y)) (q : X → Y → ℝ) : Prop :=
  ContinuousTheorem1.ContinuousCalibration μ q

/-- Theorem 2 assumes at least two classes in the finite Lean wrapper. -/
-- audit-premise: hK : 2 ≤ K
abbrev assumption_theorem2_at_least_two_classes (K : ℕ) : Prop :=
  2 ≤ K

/-- Theorem 2 states the sample-size condition `N > K`. -/
-- audit-premise: hNK : K < N
abbrev assumption_theorem2_more_rows_than_classes (N K : ℕ) : Prop :=
  K < N

/-- Positive sample size is the formal consequence of the source `N > K` condition. -/
-- audit-premise: hNpos : 0 < N
abbrev assumption_theorem2_positive_sample_count (N : ℕ) : Prop :=
  0 < N

/-- Non-trivial reference distributions are probability distributions. -/
-- audit-premise: hpref_nonneg : ∀ y, 0 ≤ pref y
abbrev assumption_theorem2_reference_nonnegative
    {K : ℕ} (pref : Fin K → ℝ) : Prop :=
  ∀ y, 0 ≤ pref y

end DSWG24DiscretizationBias
