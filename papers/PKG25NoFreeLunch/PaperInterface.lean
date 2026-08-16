import PKG25NoFreeLunch.SourceAudit
import PKG25NoFreeLunch.Assumptions
import PKG25NoFreeLunch.ParameterizedS1
import PKG25NoFreeLunch.WitnessPartitionRealization
import PKG25NoFreeLunch.JointLawFinitePartition
import PKG25NoFreeLunch.JointLawGeneralPartition
import PKG25NoFreeLunch.JointLawDependentPartition
import PKG25NoFreeLunch.JointLawMixture
import PKG25NoFreeLunch.JointSourceModel
import PKG25NoFreeLunch.Proposition9FinalMixture
import PKG25NoFreeLunch.Proposition7UniformMixture

open MeasureTheory

/-!
# Human-facing paper interface: A No Free Lunch Theorem for Human-AI Collaboration

This file exposes the source definitions, construction formulas, and named
results checked in Lean.  The source distribution is represented directly as a
joint law on `X x {0,1}`.  Because the source's point-conditioned calibration
display is under-specified on null prediction fibers, this interface uses the
explicit event-calibration interpretation recorded in the audit: calibration
holds for every measurable event in a predictor's reported probability.  The
finite adversarial witnesses embed in that universe with their actual
classifier accuracies unchanged.
-/

namespace PKG25NoFreeLunch

/-! ## General probability-space model and accuracy definitions -/

/--
The opening source display is expected absolute 0--1 loss, despite calling it
accuracy.  Lean records the correction: expected correctness is one minus that
loss.

Source status: corrected source display; see defect `PKG25-ACCURACY-LOSS-01`.
-/
theorem source_accuracy_loss_correction (prediction : Label) (eta : ℝ) :
    pointAccuracy prediction eta = 1 - pointZeroOneLoss prediction eta :=
  pointAccuracy_eq_one_sub_pointZeroOneLoss prediction eta

/--
The source collaboration setting: a probability law over input-label pairs and
calibrated probability predictors.  Calibration is stated eventwise, which is
the explicit non-vacuous interpretation of the source's conditional display on
both atomic and atomless prediction laws.
-/
abbrev source_definition_probability_collaboration_setting (n : ℕ) :=
  JointLawCollaborationSetting n

/-- Every source predictor takes values in the probability interval `[0,1]`. -/
theorem source_formula_probability_predictor_range {n : ℕ}
    (S : JointLawCollaborationSetting n)
    (i : Fin n) (x : S.X) :
    0 ≤ S.pred i x ∧ S.pred i x ≤ 1 :=
  S.pred_range i x

/--
The source calibration identity under the explicit event-calibration
interpretation.  Unlike exact-point conditioning, this remains meaningful when
the distribution of reported probabilities is atomless.
-/
theorem source_formula_probability_calibration {n : ℕ}
    (S : JointLawCollaborationSetting n)
    (i : Fin n) (A : Set ℝ) (hA : MeasurableSet A) :
    (∫ z : S.X × Label,
      ({z | S.pred i z.1 ∈ A ∧ z.2 = true}.indicator fun _ => (1 : ℝ)) z
        ∂S.joint) =
      ∫ z : S.X × Label,
        ({z | S.pred i z.1 ∈ A}.indicator fun z => S.pred i z.1) z
          ∂S.joint :=
  S.calibrated_events i A hA

/-- The source's induced individual classifier on the general setting. -/
theorem source_formula_probability_agent_classifier {n : ℕ}
    (S : JointLawCollaborationSetting n)
    (i : Fin n) (x : S.X) :
    S.agentClassifier i x = roundProb (S.pred i x) := rfl

/-- The source's expected individual accuracy as a probability-space integral. -/
theorem source_formula_probability_agent_accuracy {n : ℕ}
    (S : JointLawCollaborationSetting n)
    (i : Fin n) :
    S.agentAccuracy i =
      ∫ z : S.X × Label,
        max (S.pred i z.1) (1 - S.pred i z.1) ∂S.joint :=
  S.agentAccuracy_eq_predictionCertainty i

/-- The source's induced collaboration classifier on the general setting. -/
theorem source_formula_probability_strategy_classifier {n : ℕ}
    (S : JointLawCollaborationSetting n)
    (C : CollaborationStrategy n)
    (x : S.X) :
    S.strategyClassifier C x = C (fun i => S.pred i x) := rfl

/-- The source's expected collaboration accuracy as a joint-law integral. -/
theorem source_formula_probability_strategy_accuracy {n : ℕ}
    (S : JointLawCollaborationSetting n) (C : CollaborationStrategy n)
    (_hwell : source_assumption_strategy_expectation_well_formed S C) :
    S.strategyAccuracy C =
      ∫ z : S.X × Label,
        if S.strategyClassifier C z.1 = z.2 then (1 : ℝ) else 0 ∂S.joint :=
  rfl

/-! ## Finite witness specialization -/

/--
The paper rounds predicted probabilities to labels and takes `round(1/2)=1`.

Source status: direct source definition, theorem section lines 20--23.
-/
noncomputable abbrev source_definition_rounding_convention := roundProb

/--
Finite calibrated collaboration settings used by every adversarial witness in
the source proof.

Source status: finite specialization of source Definition 1; the source permits
arbitrary probability spaces.
-/
abbrev source_definition_finite_collaboration_setting (n : ℕ) :=
  FiniteCollaborationSetting n

/--
The finite calibration equation: label-one mass on a prediction cell equals
the cell's prediction times its probability mass.

Source status: finite-sum form of the source calibration display.
-/
theorem source_formula_finite_calibration {n : ℕ}
    (S : FiniteCollaborationSetting n) (i : Fin n) (p : ℝ) :
    eventLabelMass S.mass S.eta (fun x : S.X => S.pred i x = p) =
      p * eventMass S.mass (fun x : S.X => S.pred i x = p) :=
  FiniteCollaborationSetting.calibrated_unconditional S i p

/--
The finite partition recipe stated directly from an input-label joint PMF.
For every set of reported values, the cell conditional probabilities satisfy
the source calibration equation.  This has no auxiliary pointwise `eta`
function as an input.
-/
theorem source_partition_predictor_calibrated
    {X Cell : Type} [Fintype X] [DecidableEq X]
    [Fintype Cell] [DecidableEq Cell]
    (joint : PMF (X × Label)) (cell : X → Cell) (A : Set ℝ)
    [DecidablePred fun x : X =>
      jointPartitionPredictor (X := X) (Cell := Cell) joint cell x ∈ A] :
    (∑ z : X × Label,
      (joint z).toReal *
        (if jointPartitionPredictor (X := X) (Cell := Cell) joint cell z.1 ∈ A ∧
          z.2 = true then 1 else 0)) =
      ∑ z : X × Label,
        (joint z).toReal *
          (if jointPartitionPredictor (X := X) (Cell := Cell) joint cell z.1 ∈ A then
            jointPartitionPredictor (X := X) (Cell := Cell) joint cell z.1 else 0) := by
  classical
  exact jointPartitionPredictor_calibrated_events joint cell A

/--
The source cell formula on a measurable positive-mass cell of an arbitrary
joint law.  This is the ordinary conditional-probability ratio only when the
cell is measurable and has positive probability.

Source status: clarified source formula.  The finite measurable partition
construction below is the scope used by every proof witness.
-/
theorem source_formula_probability_partition_induced_predictor
    {X Cell : Type*} [MeasurableSpace X]
    [MeasurableSpace Cell] [MeasurableSingletonClass Cell]
    (joint : Measure (X × Label)) [IsProbabilityMeasure joint]
    (cell : X → Cell) (hcell : Measurable cell) (x : X)
    (hpositive : 0 < jointLawPartitionCellMass joint cell (cell x)) :
    jointLawPartitionPredictor joint cell x =
      jointLawPartitionCellTrueMass joint cell (cell x) /
        jointLawPartitionCellMass joint cell (cell x) :=
  by
    have _hmeasurable_cell : MeasurableSet
        (jointLawPartitionInputEvent cell (cell x)) :=
      jointLawPartitionInputEvent_measurable cell hcell (cell x)
    simp [jointLawPartitionPredictor, jointLawPartitionCellPrediction,
      ne_of_gt hpositive]

/--
The totalization used by the finite measurable partition construction: a
null cell is assigned prediction zero.  This is an explicit formalization
convention, not a value supplied by the source's conditional-probability
display; it is expectation-irrelevant on that null cell.
-/
theorem source_convention_probability_partition_zero_mass_prediction
    {X Cell : Type*} [MeasurableSpace X]
    [MeasurableSpace Cell] [MeasurableSingletonClass Cell]
    (joint : Measure (X × Label)) [IsProbabilityMeasure joint]
    (cell : X → Cell) (hcell : Measurable cell) (x : X)
    (hzero : jointLawPartitionCellMass joint cell (cell x) = 0) :
    jointLawPartitionPredictor joint cell x = 0 := by
  have _hmeasurable_cell : MeasurableSet
      (jointLawPartitionInputEvent cell (cell x)) :=
    jointLawPartitionInputEvent_measurable cell hcell (cell x)
  simp [jointLawPartitionPredictor, jointLawPartitionCellPrediction, hzero]

/--
The arbitrary finite-measurable-partition recipe is calibrated directly under
the raw input-label law.  Equal-valued cells are combined before calibration
is asserted, so this theorem also covers coincident cell conditional means.
-/
theorem source_probability_partition_predictor_calibrated
    {X Cell : Type*} [MeasurableSpace X]
    [Fintype Cell] [MeasurableSpace Cell] [MeasurableSingletonClass Cell]
    (joint : Measure (X × Label)) [IsProbabilityMeasure joint]
    (cell : X → Cell) (hcell : Measurable cell)
    (A : Set ℝ) (hA : MeasurableSet A) :
    (∫ z : X × Label,
      ({z | jointLawPartitionPredictor joint cell z.1 ∈ A ∧ z.2 = true}.indicator
        fun _ => (1 : ℝ)) z ∂joint) =
      ∫ z : X × Label,
        ({z | jointLawPartitionPredictor joint cell z.1 ∈ A}.indicator
          fun z => jointLawPartitionPredictor joint cell z.1) z ∂joint :=
  jointLawPartitionPredictor_calibrated_events joint cell hcell A hA

/-- The general partition recipe satisfies the source event-calibration identity. -/
theorem source_probability_partition_predictor_calibrated_events
    {X Cell : Type*} [MeasurableSpace X]
    [Fintype Cell] [MeasurableSpace Cell] [MeasurableSingletonClass Cell]
    (joint : Measure (X × Label)) [IsProbabilityMeasure joint]
    (cell : X → Cell) (hcell : Measurable cell)
    (A : Set ℝ) (hA : MeasurableSet A) :
    (∫ z : X × Label,
      ({z | jointLawPartitionPredictor joint cell z.1 ∈ A ∧ z.2 = true}.indicator
        fun _ => (1 : ℝ)) z ∂joint) =
      ∫ z : X × Label,
        ({z | jointLawPartitionPredictor joint cell z.1 ∈ A}.indicator
          fun z => jointLawPartitionPredictor joint cell z.1) z ∂joint :=
  source_probability_partition_predictor_calibrated joint cell hcell A hA

/--
The finite raw-joint specialization packages one partition per agent without
an input `eta` representation.
-/
noncomputable abbrev source_partition_collaboration_setting :=
  @finiteJointLawPartitionCollaborationSetting

/--
One finite measurable partition per agent constructs a calibrated setting in
the source's raw joint-law model.  The cell types may differ by agent, as in
the source's ordered tuple of partitions.
-/
noncomputable abbrev source_probability_partition_collaboration_setting :=
  @jointLawDependentPartitionSetting

/--
A collaboration strategy is a deterministic map from an `n`-agent probability
profile to a binary label.

Source status: direct source definition, theorem section lines 26--29.
-/
abbrev source_definition_collaboration_strategy (n : ℕ) :=
  CollaborationStrategy n

/--
An agent's induced classifier rounds that agent's probability prediction.

Source status: direct source formula, theorem section lines 20--23.
-/
theorem source_formula_agent_classifier {n : ℕ}
    (S : FiniteCollaborationSetting n) (i : Fin n) (x : S.X) :
    S.agentClassifier i x = roundProb (S.pred i x) := rfl

/--
Finite-sum expected-correctness formula for an individual agent's accuracy.

Source status: finite specialization of the source individual-accuracy display.
-/
theorem source_formula_agent_accuracy {n : ℕ}
    (S : FiniteCollaborationSetting n) (i : Fin n) :
    S.agentAccuracy i =
      ∑ x : S.X, S.mass x * pointAccuracy (roundProb (S.pred i x)) (S.eta x) :=
  rfl

/--
The collaboration classifier applies the strategy to the profile of agent
predictions at the input.

Source status: direct finite form of the source induced-classifier display.
-/
theorem source_formula_strategy_classifier {n : ℕ}
    (S : FiniteCollaborationSetting n) (C : CollaborationStrategy n) (x : S.X) :
    S.strategyClassifier C x = C (fun i => S.pred i x) := rfl

/--
Finite-sum expected-correctness formula for collaboration-strategy accuracy.

Source status: finite specialization of the source strategy-accuracy definition.
-/
theorem source_formula_strategy_accuracy {n : ℕ}
    (S : FiniteCollaborationSetting n) (C : CollaborationStrategy n) :
    S.strategyAccuracy C =
      ∑ x : S.X, S.mass x * pointAccuracy (C (fun i => S.pred i x)) (S.eta x) :=
  rfl

/--
Source Definition 3 under the raw joint-law, event-calibrated setting
semantics: in every calibrated setting where the strategy expectation is
well-formed, collaboration is at least as accurate as some agent.
-/
abbrev source_definition_reliable_probability {n : ℕ} :=
  @ReliableJointLaw n

/-- Exact checked expansion of source Definition 3 reliability. -/
theorem source_formula_reliable_probability_iff {n : ℕ}
    [Nonempty (Fin n)] (C : CollaborationStrategy n) :
    ReliableJointLaw C ↔
      ∀ S : JointLawCollaborationSetting n,
        source_assumption_strategy_expectation_well_formed S C →
        ∃ i : Fin n, S.agentAccuracy i ≤ S.strategyAccuracy C :=
  Iff.rfl

/--
Reliability over the finite calibrated witness class used in the checked proof.

Source status: weaker finite-witness property implied by source reliability;
proving the conclusion from it gives a logically stronger implication.
-/
abbrev source_definition_finite_reliability {n : ℕ} := @ReliableFinite n

/-- Every finite adversarial setting embeds in the source universe exactly. -/
noncomputable abbrev source_finite_setting_embedding :=
  @JointLawCollaborationSetting.ofFinite

/-- The finite embedding preserves each individual agent's exact accuracy. -/
theorem source_finite_embedding_preserves_agent_accuracy {n : ℕ}
    (S : FiniteCollaborationSetting n)
    (i : Fin n) :
    (JointLawCollaborationSetting.ofFinite S).agentAccuracy i =
      S.agentAccuracy i :=
  JointLawCollaborationSetting.ofFinite_agentAccuracy S i

/-- The finite embedding preserves the collaboration strategy's exact accuracy. -/
theorem source_finite_embedding_preserves_strategy_accuracy {n : ℕ}
    (C : CollaborationStrategy n) (S : FiniteCollaborationSetting n) :
    (JointLawCollaborationSetting.ofFinite S).strategyAccuracy C =
      S.strategyAccuracy C :=
  JointLawCollaborationSetting.ofFinite_strategyAccuracy C S

/-- General source reliability therefore implies reliability on every checked witness. -/
theorem source_bridge_probability_reliability_to_finite {n : ℕ}
    {C : CollaborationStrategy n} (hrel : ReliableJointLaw C) :
    ReliableFinite C :=
  reliableFinite_of_reliableJointLaw hrel

/--
The interior profile domain `(0,1)^n` used in non-collaboration.

Source status: direct source domain from Definition 4.
-/
abbrev source_definition_interior_prediction_profile {n : ℕ} := @Interior n

/-- Exact checked expansion of the source's interior profile domain. -/
theorem source_formula_interior_prediction_profile_iff {n : ℕ}
    (p : Fin n → ℝ) :
    Interior p ↔ ∀ i : Fin n, 0 < p i ∧ p i < 1 :=
  Iff.rfl

/--
Non-collaboration means one fixed agent off its half tie and one fixed label on
the half slice, only on interior profiles.

Source status: direct source Definition 4, including its boundary exemption.
-/
abbrev source_definition_non_collaborative {n : ℕ} := @NonCollaborative n

/-- Exact checked expansion of source Definition 4 non-collaboration. -/
theorem source_formula_non_collaborative_iff {n : ℕ}
    (C : CollaborationStrategy n) :
    NonCollaborative C ↔
      ∃ k : Fin n, ∃ α : Label,
        DefersAwayFromHalf C k ∧ ConstantOnHalfSlice C k α :=
  Iff.rfl

/-! ## Correctness and agreement vocabulary -/

/--
Source Definition 5: pointwise correctness relative to a supplied conditional
label probability.  The raw joint-law model deliberately does not choose a
pointwise conditional-probability version on arbitrary null input fibers; this
numeric vocabulary is used directly by the finite source witnesses.
-/
def source_definition_correct_on (prediction : Label) (eta : ℝ) : Prop :=
  prediction = roundProb eta

/-- Exact checked expansion of source Definition 5 correctness. -/
theorem source_formula_correct_on_iff (prediction : Label) (eta : ℝ) :
    source_definition_correct_on prediction eta ↔
      prediction = roundProb eta :=
  Iff.rfl

/-- Source Definition 5: pointwise incorrectness. Source status: direct source predicate. -/
def source_definition_incorrect_on (prediction : Label) (eta : ℝ) : Prop :=
  prediction ≠ roundProb eta

/-- Exact checked expansion of source Definition 5 incorrectness. -/
theorem source_formula_incorrect_on_iff (prediction : Label) (eta : ℝ) :
    source_definition_incorrect_on prediction eta ↔
      prediction ≠ roundProb eta :=
  Iff.rfl

/-- Source Definition 5: pointwise agreement. Source status: direct source predicate. -/
def source_definition_agree_on (prediction1 prediction2 : Label) : Prop :=
  prediction1 = prediction2

/-- Exact checked expansion of source Definition 5 agreement. -/
theorem source_formula_agree_on_iff (prediction1 prediction2 : Label) :
    source_definition_agree_on prediction1 prediction2 ↔
      prediction1 = prediction2 :=
  Iff.rfl

/-- Source Definition 5: pointwise disagreement. Source status: direct source predicate. -/
def source_definition_disagree_on (prediction1 prediction2 : Label) : Prop :=
  prediction1 ≠ prediction2

/-- Exact checked expansion of source Definition 5 disagreement. -/
theorem source_formula_disagree_on_iff (prediction1 prediction2 : Label) :
    source_definition_disagree_on prediction1 prediction2 ↔
      prediction1 ≠ prediction2 :=
  Iff.rfl

/--
The proof-preliminaries claim that one positive-mass correct/incorrect point
always yields strict accuracy dominance omits the half-tie case: under the
paper's tie convention the labels are called correct and incorrect but have
equal expected correctness at `eta=1/2`.

Source status: refutation of quarantined source defect
`PKG25-CORRECTNESS-TIE-01`; the constructed proof witnesses use `eta=0` or `1`.
-/
theorem source_correctness_strict_gap_half_tie_counterexample :
    roundProb ((1 : ℝ) / 2) = true ∧
      false ≠ roundProb ((1 : ℝ) / 2) ∧
      pointAccuracy true ((1 : ℝ) / 2) =
        pointAccuracy false ((1 : ℝ) / 2) :=
  halfTie_correct_incorrect_same_accuracy

/--
With the omitted `eta ≠ 1/2` condition restored, a correct binary prediction
is strictly more accurate than an incorrect one.

Source status: corrected source statement for
`PKG25-CORRECTNESS-TIE-01`; the added premise is automatic in the paper's
later `eta=0` and `eta=1` witness cells.
-/
theorem source_correctness_strict_gap_corrected
    {good bad : Label} {eta : ℝ}
    (hgood : source_definition_correct_on good eta)
    (hbad : source_definition_incorrect_on bad eta)
    (hne : eta ≠ (1 : ℝ) / 2) :
    pointAccuracy bad eta < pointAccuracy good eta :=
  pointAccuracy_lt_of_correct_incorrect_of_ne_half hgood hbad hne

/-! ## Proposition 6: mixtures of collaboration settings -/

/--
The source mixture scales every measurable input-label event inside component
`m` by `lambda_m` and retains each component's agent predictions.  Equality of
the full embedded joint law is the measure-theoretic replacement for the
source's point-mass and point-conditional-label displays; it also applies to
continuous distributions, where neither pointwise display is meaningful.

Source status: direct arbitrary-setting version of the three construction
formulas in the proof of Proposition 6.
-/
theorem source_formula_mixture_components
    {n ell : ℕ} (S : Fin ell → JointLawCollaborationSetting n)
    (w : Fin ell → ℝ)
    (hw_nonneg : ∀ r, 0 ≤ w r) (hw_sum : ∑ r, w r = 1)
    (r : Fin ell) (A : Set ((S r).X × Label)) (hA : MeasurableSet A)
    (z : Sigma fun r : Fin ell => (S r).X) :
    (JointLawCollaborationSetting.mix S w hw_nonneg hw_sum).joint
        ((jointLawMixtureEmbedding S r) '' A) =
        ENNReal.ofReal (w r) * (S r).joint A ∧
    (∀ i : Fin n,
      (JointLawCollaborationSetting.mix S w hw_nonneg hw_sum).pred i z =
        (S z.1).pred i z.2) := by
  exact ⟨jointLawMixtureMeasure_component_image S w r A hA, fun _ => rfl⟩

/--
Proposition 6 on the source's raw joint-law setting universe:
a finite weighted dependent disjoint union is one collaboration setting,
preserves every agent accuracy, and preserves every strategy accuracy whenever
the source expectation is well formed on the component settings.  The mixture
setting itself is independent of the strategy.

Source status: direct formalization of Proposition 6 and both displayed
accuracy equations, with the source's implicit expectation well-formedness
condition explicit.
-/
theorem source_proposition6_linear_combination_settings
    {n ell : ℕ} (S : Fin ell → JointLawCollaborationSetting n)
    (w : Fin ell → ℝ)
    (hw_nonneg : ∀ r : Fin ell, 0 ≤ w r)
    (hw_sum : ∑ r : Fin ell, w r = 1) :
    ∃ Smix : JointLawCollaborationSetting n,
      (∀ i : Fin n,
        Smix.agentAccuracy i = ∑ r : Fin ell, w r * (S r).agentAccuracy i) ∧
      (∀ C : CollaborationStrategy n,
        (∀ r : Fin ell,
          source_assumption_strategy_expectation_well_formed (S r) C) →
        source_assumption_strategy_expectation_well_formed Smix C ∧
          Smix.strategyAccuracy C =
            ∑ r : Fin ell, w r * (S r).strategyAccuracy C) := by
  refine ⟨JointLawCollaborationSetting.mix S w hw_nonneg hw_sum,
    JointLawCollaborationSetting.agentAccuracy_mix S w hw_nonneg hw_sum, ?_⟩
  intro C hC
  exact ⟨JointLawCollaborationSetting.strategyWellFormed_mix
      S w hw_nonneg hw_sum C hC,
    JointLawCollaborationSetting.strategyAccuracy_mix
      S w hw_nonneg hw_sum C hC⟩

/--
Auxiliary non-source-facing finite-witness specialization of Proposition 6,
used by the checked finite proof of Proposition 7.
-/
theorem source_proposition6_finite_linear_combination_settings
    {n ell : ℕ} (S : Fin ell → FiniteCollaborationSetting n) (w : Fin ell → ℝ)
    (hw_nonneg : ∀ r : Fin ell, 0 ≤ w r)
    (hw_sum : ∑ r : Fin ell, w r = 1) :
    ∃ Smix : FiniteCollaborationSetting n,
      (∀ i : Fin n,
        Smix.agentAccuracy i = ∑ r : Fin ell, w r * (S r).agentAccuracy i) ∧
      (∀ C : CollaborationStrategy n,
        Smix.strategyAccuracy C = ∑ r : Fin ell, w r * (S r).strategyAccuracy C) := by
  refine ⟨FiniteCollaborationSetting.mix S w hw_nonneg hw_sum, ?_, ?_⟩
  · exact FiniteCollaborationSetting.agentAccuracy_mix S w hw_nonneg hw_sum
  · exact FiniteCollaborationSetting.strategyAccuracy_mix S w hw_nonneg hw_sum

/-! ## Main theorem, Proposition 7, and the counterexample construction -/

/--
Theorem 1 over the source's raw joint-law event-calibration semantics:
reliability implies non-collaboration.

Source status: direct source-faithful forward implication.  Its proof embeds
the finite calibrated adversarial settings used by the paper exactly.
-/
theorem source_theorem1_no_free_lunch {n : ℕ} [Nonempty (Fin n)]
    (C : CollaborationStrategy n) :
    ReliableJointLaw C → NonCollaborative C :=
  main_no_free_lunch_jointLaw C

/--
The unnumbered proof-section `if and only if` is false because Definition 4
does not constrain boundary profiles.  This one-agent strategy is
non-collaborative but fails reliability on a calibrated boundary setting.

Source status: refutation of quarantined source defect
`PKG25-IFF-BOUNDARY-01`; it does not weaken Theorem 1's forward implication.
-/
theorem source_iff_converse_boundary_counterexample :
    NonCollaborative boundaryFlipStrategy ∧
      ¬ ReliableJointLaw boundaryFlipStrategy := by
  refine ⟨boundaryFlipStrategy_nonCollaborative, ?_⟩
  intro hrel
  exact boundaryFlipStrategy_not_reliableFinite
    (reliableFinite_of_reliableJointLaw hrel)

/--
Source Proposition 7: raw joint-law reliability forces one fixed agent away
from that agent's half tie.

Source status: direct source conclusion, obtained by applying source
reliability to the exact finite joint-law adversarial witnesses.
-/
theorem source_proposition7_reliability_forces_fixed_deferral
    {n : ℕ} [Nonempty (Fin n)] (C : CollaborationStrategy n) :
    ReliableJointLaw C → ∃ k : Fin n, DefersAwayFromHalf C k := by
  intro hrel
  exact reliableFinite_exists_defers_away
    (reliableFinite_of_reliableJointLaw hrel)

/--
Under the negation of Proposition 7's fixed-deferral conclusion, the source's
uniform average of one Lemma 8 witness per agent is an explicit raw joint-law
setting on which every agent strictly beats the strategy.

Source status: direct checked strict-mixture contradiction used in the proof
of Proposition 7.
-/
theorem source_proposition7_uniform_mixture_strict_counterexample
    {n : ℕ} [Nonempty (Fin n)] (C : CollaborationStrategy n)
    (hno_fixed_deferral : ¬ ∃ k : Fin n, DefersAwayFromHalf C k) :
    ∃ S : JointLawCollaborationSetting n,
      source_assumption_strategy_expectation_well_formed S C ∧
        ∀ i : Fin n, S.strategyAccuracy C < S.agentAccuracy i :=
  proposition7_raw_uniform_witness_of_no_fixed_deferral C hno_fixed_deferral

/--
Source Lemma 8: a bad interior tuple yields a collaboration setting on which
agent `k` strictly beats the strategy and every agent weakly beats it.

Source status: direct formalization of Lemma 8.
-/
theorem source_lemma8_bad_tuple_counterexample_setting
    {n : ℕ} {C : CollaborationStrategy n} {p : Fin n → ℝ} (hp : Interior p)
    {k : Fin n} (hhalf_ne : p k ≠ (1 : ℝ) / 2)
    (hbad : C p ≠ roundProb (p k)) :
    ∃ S : JointLawCollaborationSetting n,
      source_assumption_strategy_expectation_well_formed S C ∧
        S.strategyAccuracy C < S.agentAccuracy k ∧
          ∀ i : Fin n, S.strategyAccuracy C ≤ S.agentAccuracy i := by
  let T : FiniteCollaborationSetting n := part1Setting (C p) p hp
  refine ⟨JointLawCollaborationSetting.ofFinite T,
    JointLawCollaborationSetting.ofFinite_strategyWellFormed C T, ?_, ?_⟩
  · have hweak := part1Setting_weakCounterexample (C := C) hp hhalf_ne hbad
    simpa [T, FiniteCollaborationSetting.toAccuracySurface,
      JointLawCollaborationSetting.ofFinite_strategyAccuracy,
      JointLawCollaborationSetting.ofFinite_agentAccuracy] using hweak.1
  · intro i
    have hweak := part1Setting_weakCounterexample (C := C) hp hhalf_ne hbad
    simpa [T, FiniteCollaborationSetting.toAccuracySurface,
      JointLawCollaborationSetting.ofFinite_strategyAccuracy,
      JointLawCollaborationSetting.ofFinite_agentAccuracy] using hweak.2 i

/--
The Lemma 8 witness uses the source's two odds formulas and common denominator.

Source status: direct finite formulas from the Lemma 8 construction.
-/
theorem source_formula_lemma8_masses
    {n : ℕ} (b : Label) (p : Fin n → ℝ) (i : Fin n) :
    part1Odds false (p i) = (1 - p i) / p i ∧
      part1Odds true (p i) = p i / (1 - p i) ∧
      part1Mass b p none = 1 / part1Denom b p ∧
      part1Mass b p (some i) = part1Odds b (p i) / part1Denom b p ∧
      part1Denom b p = 1 + ∑ j : Fin n, part1Odds b (p j) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/--
The Lemma 8 witness's label probabilities and partition-induced predictions.

Source status: direct finite formulas from the Lemma 8 construction.
-/
theorem source_formula_lemma8_labels_and_predictions
    {n : ℕ} (b : Label) (p : Fin n → ℝ) (i j : Fin n) :
    part1Eta b (none : Part1Point n) = labelReal (!b) ∧
      part1Eta b (some j) = labelReal b ∧
      part1Pred b p i none = p i ∧
      part1Pred b p i (some j) = if j = i then p i else labelReal b := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/--
The exact Lemma 8 source partition is realized by the raw finite joint-law
constructor: agent `i` pools `{0,i}` and leaves every other point singleton.
Its conditional cell probabilities are precisely the displayed predictor.

Source status: checked construction provenance for `proof.tex`, lines 99--106
and 129--133; this is not merely a direct definition of the predictor formula.
-/
theorem source_lemma8_partition_realization {n : ℕ} (b : Label)
    (p : Fin n → ℝ) (hp : Interior p) :
    ∀ (i : Fin n) (x : Part1Point n),
      (finiteJointLawPartitionCollaborationSetting
        (finiteJointLawPMF (part1Setting b p hp))
        (fun j : Fin n => part1SourceCell j)).pred i x =
          part1Pred b p i x := by
  intro i x
  rw [finiteJointLawPartitionCollaborationSetting_pred]
  exact part1SourceCell_rawPartitionPredictor_eq hp i x

/--
The finite Lemma 8 construction is calibrated for every agent.

Source status: checked finite counterpart of the partition-calibration step for
the paper's specific witness; the fully general probability-space partition
recipe is exposed earlier as
`source_probability_partition_predictor_calibrated`.
-/
theorem source_lemma8_witness_calibrated {n : ℕ} (b : Label)
    (p : Fin n → ℝ) (hp : Interior p) :
    ∀ i : Fin n, ∀ r : ℝ,
      eventLabelMass (part1Mass b p) (part1Eta b)
          (fun x : Part1Point n => part1Pred b p i x = r) =
        r * eventMass (part1Mass b p)
          (fun x : Part1Point n => part1Pred b p i x = r) := by
  intro i r
  simpa [part1Setting] using
    FiniteCollaborationSetting.calibrated_unconditional (part1Setting b p hp) i r

/-! ## Proposition 9: the two tie-slice settings -/

/--
The displayed algebraic formulas and calibration equation for the first
Proposition 9 family.  The next row records the additional positivity needed
for this formula to define a valid probability setting with interior profiles.
-/
theorem source_formula_proposition9_s1_family {n : ℕ} {ε : ℝ}
    (hεhalf : ε < (1 : ℝ) / 2) (k : Fin n) :
    part2S1ParamMass false = (1 : ℝ) / 3 ∧
      part2S1ParamMass true = (2 : ℝ) / 3 ∧
      part2S1ParamEta ε false = ε ∧
      part2S1ParamEta ε true = 1 - ε ∧
      part2S1ParamKPred ε = (2 : ℝ) / 3 - ε / 3 ∧
      (∀ (i : Fin n) (x : Part2S1ParamPoint),
        part2S1ParamPred ε k i x =
          if i = k then part2S1ParamKPred ε else part2S1ParamEta ε x) ∧
      (∀ (i : Fin n) (r : ℝ),
        eventMass part2S1ParamMass
            (fun x : Part2S1ParamPoint => part2S1ParamPred ε k i x = r) > 0 →
          eventLabelMass part2S1ParamMass (part2S1ParamEta ε)
              (fun x : Part2S1ParamPoint => part2S1ParamPred ε k i x = r) =
            r * eventMass part2S1ParamMass
              (fun x : Part2S1ParamPoint =>
                part2S1ParamPred ε k i x = r)) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, part2S1Param_calibrated hεhalf k⟩
  intro i x
  rfl

/--
The Proposition 9 first setting is a valid probability/interior construction
under the implicit source-domain condition `0 < epsilon < 1/2`.  The source
prints only the upper bound while also using these values as probabilities and
as profiles in `(0,1)^n`.

Source status: explicit additional source-domain convention; it does not
change the Proposition 9 conclusion.
-/
theorem source_proposition9_s1_positive_parameter_validity
    {n : ℕ} {ε : ℝ} (hε0 : 0 < ε) (hεhalf : ε < (1 : ℝ) / 2)
    (k : Fin n) :
    (∀ x : Part2S1ParamPoint,
      0 ≤ part2S1ParamEta ε x ∧ part2S1ParamEta ε x ≤ 1) ∧
      (∀ (i : Fin n) (x : Part2S1ParamPoint),
        0 ≤ part2S1ParamPred ε k i x ∧ part2S1ParamPred ε k i x ≤ 1) ∧
      ∀ x : Part2S1ParamPoint,
        Interior (fun i : Fin n => part2S1ParamPred ε k i x) := by
  exact ⟨part2S1ParamEta_range hε0 hεhalf,
    part2S1ParamPred_range hε0 hεhalf k,
    part2S1Param_profile_interior hε0 hεhalf k⟩

/--
The exact first Proposition 9 source partition is realized by the raw finite
joint-law constructor: agent `k` pools both points and all other agents use
singleton cells.  The resulting cell probabilities are the S1 predictors.

Source status: checked construction provenance for `proof.tex`, lines 174--182.
-/
theorem source_proposition9_s1_partition_realization {n : ℕ} {ε : ℝ}
    (hε0 : 0 < ε) (hεhalf : ε < (1 : ℝ) / 2) (k : Fin n) :
    ∀ (i : Fin n) (x : Part2S1ParamPoint),
      (finiteJointLawPartitionCollaborationSetting
        (finiteJointLawPMF (part2S1ParamSetting ε hε0 hεhalf k))
        (fun j : Fin n => part2S1ParamSourceCell k j)).pred i x =
          part2S1ParamPred ε k i x := by
  intro i x
  rw [finiteJointLawPartitionCollaborationSetting_pred]
  exact part2S1ParamSourceCell_rawPartitionPredictor_eq hε0 hεhalf k i x

/--
For every source parameter, the collaboration strategy and agent `k` have
the same accuracy `2/3-epsilon/3`, while every other agent has accuracy
`1-epsilon` and is strictly more accurate.
-/
theorem source_proposition9_s1_parameterized_accuracy_gap {n : ℕ} {ε : ℝ}
    (hε0 : 0 < ε) (hεhalf : ε < (1 : ℝ) / 2)
    {C : CollaborationStrategy n} {k : Fin n}
    (hk : DefersAwayFromHalf C k) :
    (part2S1ParamSetting ε hε0 hεhalf k).strategyAccuracy C =
        (2 : ℝ) / 3 - ε / 3 ∧
      (part2S1ParamSetting ε hε0 hεhalf k).agentAccuracy k =
        (2 : ℝ) / 3 - ε / 3 ∧
      (∀ i : Fin n, i ≠ k →
        (part2S1ParamSetting ε hε0 hεhalf k).agentAccuracy i = 1 - ε ∧
        (part2S1ParamSetting ε hε0 hεhalf k).strategyAccuracy C <
          (part2S1ParamSetting ε hε0 hεhalf k).agentAccuracy i) := by
  refine ⟨part2S1Param_strategyAccuracy hε0 hεhalf hk,
    part2S1Param_agentAccuracy_k hε0 hεhalf k, ?_⟩
  intro i hik
  refine ⟨part2S1Param_agentAccuracy_ne hε0 hεhalf hik, ?_⟩
  exact (part2S1Param_accuracy_gap hε0 hεhalf hk).2 i hik

/--
The original `epsilon=1/4` specialization, retained as a concrete regression
check for the parameterized construction:
masses `1/3,2/3`, conditional label probabilities `1/4,3/4`, and constant
agent-`k` prediction `7/12`.

Source status: exact specialization, now subsumed by the preceding full family.
-/
theorem source_formula_proposition9_s1_specialization {n : ℕ} (k : Fin n) :
    part2S1Mass false = (1 : ℝ) / 3 ∧
      part2S1Mass true = (2 : ℝ) / 3 ∧
      part2S1Eta false = (1 : ℝ) / 4 ∧
      part2S1Eta true = (3 : ℝ) / 4 ∧
      part2S1KPred = (7 : ℝ) / 12 ∧
      (∀ (i : Fin n) (x : Part2S1Point),
        part2S1Pred k i x =
          if i = k then part2S1KPred else part2S1Eta x) ∧
      (∀ (i : Fin n) (r : ℝ),
        eventMass part2S1Mass
            (fun x : Part2S1Point => part2S1Pred k i x = r) > 0 →
          eventLabelMass part2S1Mass part2S1Eta
              (fun x : Part2S1Point => part2S1Pred k i x = r) =
            r * eventMass part2S1Mass
              (fun x : Part2S1Point => part2S1Pred k i x = r)) := by
  refine ⟨by norm_num [part2S1Mass], by norm_num [part2S1Mass],
    by norm_num [part2S1Eta], by norm_num [part2S1Eta],
    by norm_num [part2S1KPred], ?_, part2S1_calibrated k⟩
  intro i x
  rfl

/--
At the concrete `epsilon=1/4` specialization, strategy and agent `k` have
accuracy `7/12`, while every other agent has accuracy `3/4`.

Source status: exact specialization, retained as a regression check.
-/
theorem source_proposition9_s1_accuracy_gap {n : ℕ}
    {C : CollaborationStrategy n} {k : Fin n} (hk : DefersAwayFromHalf C k) :
    (part2S1Setting k).strategyAccuracy C = (7 : ℝ) / 12 ∧
      (part2S1Setting k).agentAccuracy k = (7 : ℝ) / 12 ∧
      (∀ i : Fin n, i ≠ k →
        (part2S1Setting k).agentAccuracy i = (3 : ℝ) / 4) := by
  exact ⟨part2S1_strategyAccuracy hk, part2S1_agentAccuracy_k k,
    fun _ hik => part2S1_agentAccuracy_ne hik⟩

/--
The corrected S2 common normalizer.  The source display leaves `j` free in
the `q`-odds term; this is the intended normalization that sums both odds
families and is required for the displayed masses to form a probability law.

Source status: corrected source formula for the local free-index typo in
`proof.tex`, lines 195--201.
-/
theorem source_formula_proposition9_s2_repaired_normalizer
    {n : ℕ} (p q : Fin n → ℝ) :
    part2S2Denom p q =
      (2 : ℝ) + ∑ j : Fin n,
        (p j / (1 - p j) + (1 - q j) / q j) := by
  unfold part2S2Denom part1Denom
  simp [part1Odds, Finset.sum_add_distrib]
  ring

/--
With the repaired common normalizer and interior profile hypotheses, the S2
mass function is a probability distribution.

Source status: checked normalization obligation for the repaired S2 formula.
-/
theorem source_proposition9_s2_repaired_mass_normalized
    {n : ℕ} {p q : Fin n → ℝ} (hp : Interior p) (hq : Interior q) :
    (∑ x : Part2S2Point n, part2S2Mass p q x) = 1 :=
  part2S2Mass_sum hp hq

/--
The source S2 construction's paired copies use the corrected normalized odds
masses, binary label probabilities, and partition-induced predictors.

Source status: corrected finite implementation of the S2 construction
formulas; the common normalizer repair is exposed immediately above.
-/
theorem source_formula_proposition9_s2_construction
    {n : ℕ} (k : Fin n) (p q : Fin n → ℝ) (i : Fin n)
    (x : Part1Point n) :
    part2S2WeightP p q =
        part1Denom true p / (part1Denom true p + part1Denom false q) ∧
      part2S2WeightQ p q =
        part1Denom false q / (part1Denom true p + part1Denom false q) ∧
      part2S2Mass p q (false, x) = part2S2WeightP p q * part1Mass true p x ∧
      part2S2Mass p q (true, x) = part2S2WeightQ p q * part1Mass false q x ∧
      part2S2Eta (false, x) = part1Eta true x ∧
      part2S2Eta (true, x) = part1Eta false x ∧
      part2S2Pred k p q i (false, x) =
        (if i = k then
          match x with
          | none => (1 : ℝ) / 2
          | some _ => part1Eta true x
        else part1Pred true p i x) ∧
      part2S2Pred k p q i (true, x) =
        (if i = k then
          match x with
          | none => (1 : ℝ) / 2
          | some _ => part1Eta false x
        else part1Pred false q i x) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
The exact second Proposition 9 source partitions are realized by the raw
finite joint-law constructor.  Agent `k` pools the two center points; every
other agent pools the two points in each copy associated with its coordinate.
The resulting cell probabilities are the displayed S2 predictors.

Source status: checked construction provenance for `proof.tex`, lines 212--217,
using the repaired normalized S2 law.
-/
theorem source_proposition9_s2_partition_realization {n : ℕ}
    {p q : Fin n → ℝ} (hp : Interior p) (hq : Interior q) (k : Fin n) :
    ∀ (i : Fin n) (x : Part2S2Point n),
      (finiteJointLawPartitionCollaborationSetting
        (finiteJointLawPMF (part2S2Setting k p q hp hq))
        (fun j : Fin n => part2S2SourceCell k j)).pred i x =
          part2S2Pred k p q i x := by
  intro i x
  rw [finiteJointLawPartitionCollaborationSetting_pred]
  exact part2S2SourceCell_rawPartitionPredictor_eq hp hq k i x

/--
The S2 predictor is calibrated for every agent.

Source status: direct finite counterpart of the two displayed S2 conditional
calibration equations and the partition construction.
-/
theorem source_proposition9_s2_calibrated {n : ℕ}
    {p q : Fin n → ℝ} (hp : Interior p) (hq : Interior q) (k : Fin n) :
    ∀ i : Fin n, ∀ r : ℝ,
      eventLabelMass (part2S2Mass p q) part2S2Eta
          (fun x : Part2S2Point n => part2S2Pred k p q i x = r) =
        r * eventMass (part2S2Mass p q)
          (fun x : Part2S2Point n => part2S2Pred k p q i x = r) := by
  intro i r
  by_cases hik : i = k
  · subst i
    exact part2S2_calibrated_k hp hq k r
  · exact part2S2_calibrated_ne hp hq hik r

/--
Opposite collaboration outputs at two interior half-slice profiles produce the
source S2 strict accuracy gap in favor of agent `k`.

Source status: direct formalization of the source S2 strict-gap conclusion.
-/
theorem source_proposition9_s2_strict_gap {n : ℕ}
    {C : CollaborationStrategy n} {k : Fin n} {p q : Fin n → ℝ}
    (hp : Interior p) (hq : Interior q)
    (hpk : p k = (1 : ℝ) / 2) (hqk : q k = (1 : ℝ) / 2)
    (hCp : C p = true) (hCq : C q = false) :
    (fun i : Fin n =>
        part2S2Pred k p q i (false, (none : Part1Point n))) = p ∧
      (fun i : Fin n =>
        part2S2Pred k p q i (true, (none : Part1Point n))) = q ∧
      (part2S2Setting k p q hp hq).strategyAccuracy C <
        (part2S2Setting k p q hp hq).agentAccuracy k :=
  ⟨part2S2_profile_false_none hpk, part2S2_profile_true_none hqk,
    part2S2_strategyAccuracy_lt_agentK hp hq hpk hqk hCp hCq⟩

/--
Source Proposition 9: fixed deferral plus raw joint-law reliability forces a
constant tie label.

Source status: direct source conclusion, obtained by applying source
reliability to the exact finite joint-law adversarial witnesses.  Lean uses
explicit final mixture weights `7/8` and `1/8` in the proof.
-/
theorem source_proposition9_reliability_forces_fixed_tie_label
    {n : ℕ} [Nonempty (Fin n)] (C : CollaborationStrategy n) (k : Fin n)
    (hrel : ReliableJointLaw C) (hk : DefersAwayFromHalf C k) :
    ∃ alpha : Label, ConstantOnHalfSlice C k alpha :=
  reliableFinite_constant_on_half (reliableFinite_of_reliableJointLaw hrel) hk

/--
The checked Proposition 9 proof instantiates the source's final mixture with
weights `7/8` and `1/8`; both agent and strategy accuracies obey the displayed
componentwise mixture equations.

Source status: explicit checked witness for the source phrase "lambda
sufficiently close to one."
-/
theorem source_formula_proposition9_explicit_final_mixture {n : ℕ}
    (S1 S2 : FiniteCollaborationSetting n) :
    ∃ Smix : JointLawCollaborationSetting n,
      (∀ i : Fin n,
        Smix.agentAccuracy i =
          (7 : ℝ) / 8 * S1.agentAccuracy i +
            (1 : ℝ) / 8 * S2.agentAccuracy i) ∧
      (∀ C : CollaborationStrategy n,
        source_assumption_strategy_expectation_well_formed Smix C ∧
          Smix.strategyAccuracy C =
            (7 : ℝ) / 8 * S1.strategyAccuracy C +
              (1 : ℝ) / 8 * S2.strategyAccuracy C) := by
  let T : Fin 2 → FiniteCollaborationSetting n := fun r =>
    if r = 0 then S1 else S2
  let w : Fin 2 → ℝ := fun r =>
    if r = 0 then (7 : ℝ) / 8 else (1 : ℝ) / 8
  have hw_nonneg : ∀ r : Fin 2, 0 ≤ w r := by
    intro r
    fin_cases r <;> norm_num [w]
  have hw_sum : ∑ r : Fin 2, w r = 1 := by
    norm_num [w]
  let Smix : FiniteCollaborationSetting n :=
    FiniteCollaborationSetting.mix T w hw_nonneg hw_sum
  refine ⟨JointLawCollaborationSetting.ofFinite Smix, ?_, ?_⟩
  · intro i
    rw [JointLawCollaborationSetting.ofFinite_agentAccuracy,
      FiniteCollaborationSetting.agentAccuracy_mix T w hw_nonneg hw_sum i]
    norm_num [Smix, T, w]
  · intro C
    refine ⟨JointLawCollaborationSetting.ofFinite_strategyWellFormed C Smix, ?_⟩
    rw [JointLawCollaborationSetting.ofFinite_strategyAccuracy,
      FiniteCollaborationSetting.strategyAccuracy_mix T w hw_nonneg hw_sum C]
    norm_num [Smix, T, w]

/--
The source's final Proposition 9 mixture is an actual strict counterexample,
not only a componentwise accounting identity.  The checked finite witness uses
the explicit weights `7/8` and `1/8`, then embeds unchanged into the raw
joint-law source universe.

Source status: direct checked witness for the final strict-inequality step of
the Proposition 9 proof.
-/
theorem source_proposition9_explicit_final_mixture_strict_counterexample
    {n : ℕ} [Nonempty (Fin n)] {C : CollaborationStrategy n} {k : Fin n}
    {p q : Fin n → ℝ} (hk : DefersAwayFromHalf C k)
    (hp : Interior p) (hq : Interior q)
    (hpk : p k = (1 : ℝ) / 2) (hqk : q k = (1 : ℝ) / 2)
    (hCp : C p = true) (hCq : C q = false) :
    ∃ Smix : JointLawCollaborationSetting n,
      source_assumption_strategy_expectation_well_formed Smix C ∧
        ∀ i : Fin n, Smix.strategyAccuracy C < Smix.agentAccuracy i := by
  let T : FiniteCollaborationSetting n := proposition9FinalMixture k p q hp hq
  refine ⟨JointLawCollaborationSetting.ofFinite T,
    JointLawCollaborationSetting.ofFinite_strategyWellFormed C T, ?_⟩
  intro i
  simpa [T, JointLawCollaborationSetting.ofFinite_strategyAccuracy,
    JointLawCollaborationSetting.ofFinite_agentAccuracy] using
    (proposition9FinalMixture_strategyAccuracy_lt_agentAccuracy
      (C := C) (k := k) (p := p) (q := q) hk hp hq hpk hqk hCp hCq i)

end PKG25NoFreeLunch
