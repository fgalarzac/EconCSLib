import GJ19OptimalBinaryRatingSystems.AppendixB
import GJ19OptimalBinaryRatingSystems.SourceDefinitions
import Mathlib.Probability.StrongLaw

/-!
# Stochastic experiment layer for Appendix B.5

The existing Appendix B development proves the deterministic finite-uniform
and Lipschitz-mesh steps.  This module supplies the preceding probabilistic
step from the primitive experiment observations: pairwise-independent IID
responses converge almost surely by the strong law, simultaneously over each
fixed finite item-question set.

For UnknownTypeExperiment, rank recovery additionally requires the expected
aggregate score to strictly identify the true quality ordering.  The printed
source uses only Lipschitz continuity (and informally says the response is
increasing); weak monotonicity permits ties and is insufficient.  The explicit
strict-order premise below is therefore a minor implied assumption, not a
paper caveat.
-/

open scoped BigOperators Function ProbabilityTheory

namespace GJ19OptimalBinaryRatingSystems

noncomputable section

open Filter MeasureTheory Topology

/-- Empirical mean used by the known- and unknown-type experiments. -/
def sourceExperimentEmpiricalMean
    {Ω : Type*} (observation : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  (∑ n ∈ Finset.range N, observation n ω) / N

/-- The source count ratio is the ratio of the two normalized sample means. -/
theorem sourceExperimentEmpiricalQuestionResponse_eq_ratio_means
    {Ω Item Y : Type*} [DecidableEq Y]
    (E : SourceRandomQuestionExperiment Ω Item Y)
    (i : Item) (y : Y) (N : ℕ) (ω : Ω) :
    sourceExperimentEmpiricalQuestionResponse E i y N ω =
      sourceExperimentEmpiricalMean
          (sourceQuestionPositiveIndicator E i y) N ω /
        sourceExperimentEmpiricalMean
          (sourceQuestionAskedIndicator E i y) N ω := by
  by_cases hN : N = 0
  · subst N
    simp [sourceExperimentEmpiricalQuestionResponse,
      sourceExperimentPositiveQuestionCount, sourceExperimentQuestionCount,
      sourceExperimentEmpiricalMean]
  · have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    simpa [sourceExperimentEmpiricalQuestionResponse,
      sourceExperimentEmpiricalMean,
      sourceExperimentPositiveQuestionCount,
      sourceExperimentQuestionCount] using
        (div_div_div_cancel_right₀ hNreal
          (sourceExperimentPositiveQuestionCount E i y N ω)
          (sourceExperimentQuestionCount E i y N ω)).symm

/--
Literal random-question SLLN for the source experiment.  Positive mass on
each question makes the empirical conditional positive-response frequency
converge to `ψ(θᵢ,y)` even though the number of question-`y` observations is
itself random.
-/
theorem lemmaB2_knownTypeExperiment_ae_question_response_of_iid
    {Ω Representative Y : Type*} [MeasurableSpace Ω]
    [Fintype Representative] [Fintype Y] [DecidableEq Y]
    (P : Measure Ω)
    (E : SourceRandomQuestionExperiment Ω Representative Y)
    (quality : Representative → ℝ) (ψ : ℝ → Y → ℝ) (H : Y → ℝ)
    (hHpos : ∀ y : Y, 0 < H y)
    (hasked_integrable :
      ∀ i : Representative, ∀ y : Y,
        Integrable (sourceQuestionAskedIndicator E i y 0) P)
    (hasked_indep :
      ∀ i : Representative, ∀ y : Y,
        Pairwise ((· ⟂ᵢ[P] ·) on sourceQuestionAskedIndicator E i y))
    (hasked_ident :
      ∀ i : Representative, ∀ y : Y, ∀ n : ℕ,
        ProbabilityTheory.IdentDistrib
          (sourceQuestionAskedIndicator E i y n)
          (sourceQuestionAskedIndicator E i y 0) P P)
    (hasked_mean :
      ∀ i : Representative, ∀ y : Y,
        ∫ ω, sourceQuestionAskedIndicator E i y 0 ω ∂P = H y)
    (hpositive_integrable :
      ∀ i : Representative, ∀ y : Y,
        Integrable (sourceQuestionPositiveIndicator E i y 0) P)
    (hpositive_indep :
      ∀ i : Representative, ∀ y : Y,
        Pairwise ((· ⟂ᵢ[P] ·) on sourceQuestionPositiveIndicator E i y))
    (hpositive_ident :
      ∀ i : Representative, ∀ y : Y, ∀ n : ℕ,
        ProbabilityTheory.IdentDistrib
          (sourceQuestionPositiveIndicator E i y n)
          (sourceQuestionPositiveIndicator E i y 0) P P)
    (hpositive_mean :
      ∀ i : Representative, ∀ y : Y,
        ∫ ω, sourceQuestionPositiveIndicator E i y 0 ω ∂P =
          H y * ψ (quality i) y) :
    ∀ᵐ ω ∂P, ∀ i : Representative, ∀ y : Y,
      Tendsto
        (fun N : ℕ =>
          sourceExperimentEmpiricalQuestionResponse E i y N ω)
        atTop (nhds (ψ (quality i) y)) := by
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro y
  filter_upwards
    [ProbabilityTheory.strong_law_ae_real
      (sourceQuestionAskedIndicator E i y)
      (hasked_integrable i y) (hasked_indep i y) (hasked_ident i y),
    ProbabilityTheory.strong_law_ae_real
      (sourceQuestionPositiveIndicator E i y)
      (hpositive_integrable i y) (hpositive_indep i y)
      (hpositive_ident i y)] with ω hasked hpositive
  have hasked' :
      Tendsto
        (fun N : ℕ => sourceExperimentEmpiricalMean
          (sourceQuestionAskedIndicator E i y) N ω)
        atTop (nhds (H y)) := by
    simpa [sourceExperimentEmpiricalMean, hasked_mean i y] using hasked
  have hpositive' :
      Tendsto
        (fun N : ℕ => sourceExperimentEmpiricalMean
          (sourceQuestionPositiveIndicator E i y) N ω)
        atTop (nhds (H y * ψ (quality i) y)) := by
    simpa [sourceExperimentEmpiricalMean, hpositive_mean i y] using hpositive
  simpa [sourceExperimentEmpiricalQuestionResponse_eq_ratio_means,
    (hHpos y).ne'] using hpositive'.div hasked' (hHpos y).ne'

/--
Strong-law step for every coordinate of a fixed finite representative/question
experiment.  Each coordinate is derived from primitive pairwise-independent
IID observations whose expectation is the corresponding source response.
-/
theorem lemmaB2_knownTypeExperiment_ae_pointwise_of_iid
    {Ω Representative Y : Type*} [MeasurableSpace Ω]
    [Fintype Representative] [Fintype Y]
    (P : Measure Ω)
    (quality : Representative → ℝ) (ψ : ℝ → Y → ℝ)
    (observation : Representative → Y → ℕ → Ω → ℝ)
    (hintegrable :
      ∀ i : Representative, ∀ y : Y,
        Integrable (observation i y 0) P)
    (hindep :
      ∀ i : Representative, ∀ y : Y,
        Pairwise ((· ⟂ᵢ[P] ·) on observation i y))
    (hident :
      ∀ i : Representative, ∀ y : Y, ∀ n : ℕ,
        ProbabilityTheory.IdentDistrib
          (observation i y n) (observation i y 0) P P)
    (hmean :
      ∀ i : Representative, ∀ y : Y,
        ∫ ω, observation i y 0 ω ∂P = ψ (quality i) y) :
    ∀ᵐ ω ∂P, ∀ i : Representative, ∀ y : Y,
      Tendsto
        (fun N : ℕ => sourceExperimentEmpiricalMean (observation i y) N ω)
        atTop (nhds (ψ (quality i) y)) := by
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro y
  simpa [sourceExperimentEmpiricalMean, hmean i y] using
    ProbabilityTheory.strong_law_ae_real
      (observation i y) (hintegrable i y) (hindep i y) (hident i y)

/--
Lemma B.2's fixed-finite uniform SLLN conclusion, now derived rather than
assumed.  Almost surely, empirical responses converge uniformly over all
representative-item/question coordinates.
-/
theorem lemmaB2_knownTypeExperiment_ae_finite_uniform_of_iid
    {Ω Representative Y : Type*} [MeasurableSpace Ω]
    [Fintype Representative] [Fintype Y]
    (P : Measure Ω)
    (quality : Representative → ℝ) (ψ : ℝ → Y → ℝ)
    (observation : Representative → Y → ℕ → Ω → ℝ)
    (hintegrable :
      ∀ i : Representative, ∀ y : Y,
        Integrable (observation i y 0) P)
    (hindep :
      ∀ i : Representative, ∀ y : Y,
        Pairwise ((· ⟂ᵢ[P] ·) on observation i y))
    (hident :
      ∀ i : Representative, ∀ y : Y, ∀ n : ℕ,
        ProbabilityTheory.IdentDistrib
          (observation i y n) (observation i y 0) P P)
    (hmean :
      ∀ i : Representative, ∀ y : Y,
        ∫ ω, observation i y 0 ω ∂P = ψ (quality i) y) :
    ∀ᵐ ω ∂P,
      TendstoUniformlyOn
        (fun N : ℕ => fun p : Representative × Y =>
          sourceExperimentEmpiricalMean (observation p.1 p.2) N ω)
        (fun p : Representative × Y => ψ (quality p.1) p.2)
        atTop Set.univ := by
  filter_upwards
    [lemmaB2_knownTypeExperiment_ae_pointwise_of_iid
      P quality ψ observation hintegrable hindep hident hmean] with ω hω
  exact
    lemmaB2_knownTypeExperiment_finite_representatives_uniform_of_pointwise
      (fun N i y => sourceExperimentEmpiricalMean (observation i y) N ω)
      (fun i y => ψ (quality i) y) hω

/--
Finite deterministic rank-stability lemma: pointwise convergence to a strictly
increasing expected score implies that empirical scores are eventually
strictly increasing in the true item order.
-/
theorem eventually_strictMono_finite_scores_of_tendsto
    {L : ℕ}
    (scoreHat : ℕ → Fin L → ℝ) (expectedScore : Fin L → ℝ)
    (hstrict : StrictMono expectedScore)
    (hpoint :
      ∀ i : Fin L,
        Tendsto (fun N : ℕ => scoreHat N i) atTop (nhds (expectedScore i))) :
    ∀ᶠ N : ℕ in atTop, StrictMono (scoreHat N) := by
  have hpair :
      ∀ i j : Fin L, i < j →
        ∀ᶠ N : ℕ in atTop, scoreHat N i < scoreHat N j := by
    intro i j hij
    let midpoint : ℝ := (expectedScore i + expectedScore j) / 2
    have hlimit : expectedScore i < expectedScore j := hstrict hij
    have hi_mid : expectedScore i < midpoint := by
      dsimp [midpoint]
      linarith
    have hmid_j : midpoint < expectedScore j := by
      dsimp [midpoint]
      linarith
    filter_upwards
      [(hpoint i).eventually_lt_const hi_mid,
        (hpoint j).eventually_const_lt hmid_j] with N hi hj
    exact hi.trans hj
  have hall :
      ∀ᶠ N : ℕ in atTop, ∀ i j : Fin L, i < j → scoreHat N i < scoreHat N j := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    by_cases hij : i < j
    · exact (hpair i j hij).mono (fun _N h _ => h)
    · exact Filter.Eventually.of_forall (fun _N h => (hij h).elim)
  exact hall.mono (fun _N hN _i _j hij => hN _i _j hij)

/--
UnknownTypeExperiment ranking step from primitive IID aggregate-score
observations.  Strict increase of expected score is the required
quality-identifiability condition omitted from the printed statement.
-/
theorem lemmaB3_unknownTypeExperiment_ae_eventual_true_order_of_iid
    {Ω : Type*} {L : ℕ} [MeasurableSpace Ω]
    (P : Measure Ω)
    (scoreObservation : Fin L → ℕ → Ω → ℝ)
    (expectedScore : Fin L → ℝ)
    (hstrict : StrictMono expectedScore)
    (hintegrable : ∀ i : Fin L, Integrable (scoreObservation i 0) P)
    (hindep :
      ∀ i : Fin L, Pairwise ((· ⟂ᵢ[P] ·) on scoreObservation i))
    (hident :
      ∀ i : Fin L, ∀ n : ℕ,
        ProbabilityTheory.IdentDistrib
          (scoreObservation i n) (scoreObservation i 0) P P)
    (hmean :
      ∀ i : Fin L,
        ∫ ω, scoreObservation i 0 ω ∂P = expectedScore i) :
    ∀ᵐ ω ∂P,
      ∀ᶠ N : ℕ in atTop,
        StrictMono (fun i : Fin L =>
          sourceExperimentEmpiricalMean (scoreObservation i) N ω) := by
  have hslln :
      ∀ᵐ ω ∂P, ∀ i : Fin L,
        Tendsto
          (fun N : ℕ =>
            sourceExperimentEmpiricalMean (scoreObservation i) N ω)
          atTop (nhds (expectedScore i)) := by
    rw [ae_all_iff]
    intro i
    simpa [sourceExperimentEmpiricalMean, hmean i] using
      ProbabilityTheory.strong_law_ae_real
        (scoreObservation i) (hintegrable i) (hindep i) (hident i)
  filter_upwards [hslln] with ω hω
  exact
    eventually_strictMono_finite_scores_of_tendsto
      (fun N i => sourceExperimentEmpiricalMean (scoreObservation i) N ω)
      expectedScore hstrict hω

/--
Literal random-question version of Lemma B.3 for a fixed finite item set.
The same match records estimate each conditional question response and the
aggregate positive-score ordering.  Strict monotonicity of the source mixed
expected score is the explicit order-identifiability premise.
-/
theorem lemmaB3_unknownTypeExperiment_ae_random_question_response_and_rank_of_iid
    {Ω Y : Type*} {L : ℕ} [MeasurableSpace Ω]
    [Fintype Y] [DecidableEq Y]
    (P : Measure Ω)
    (E : SourceRandomQuestionExperiment Ω (Fin L) Y)
    (quality : Fin L → ℝ) (ψ : ℝ → Y → ℝ) (H : Y → ℝ)
    (hHpos : ∀ y : Y, 0 < H y)
    (hasked_integrable :
      ∀ i : Fin L, ∀ y : Y,
        Integrable (sourceQuestionAskedIndicator E i y 0) P)
    (hasked_indep :
      ∀ i : Fin L, ∀ y : Y,
        Pairwise ((· ⟂ᵢ[P] ·) on sourceQuestionAskedIndicator E i y))
    (hasked_ident :
      ∀ i : Fin L, ∀ y : Y, ∀ n : ℕ,
        ProbabilityTheory.IdentDistrib
          (sourceQuestionAskedIndicator E i y n)
          (sourceQuestionAskedIndicator E i y 0) P P)
    (hasked_mean :
      ∀ i : Fin L, ∀ y : Y,
        ∫ ω, sourceQuestionAskedIndicator E i y 0 ω ∂P = H y)
    (hpositive_integrable :
      ∀ i : Fin L, ∀ y : Y,
        Integrable (sourceQuestionPositiveIndicator E i y 0) P)
    (hpositive_indep :
      ∀ i : Fin L, ∀ y : Y,
        Pairwise ((· ⟂ᵢ[P] ·) on sourceQuestionPositiveIndicator E i y))
    (hpositive_ident :
      ∀ i : Fin L, ∀ y : Y, ∀ n : ℕ,
        ProbabilityTheory.IdentDistrib
          (sourceQuestionPositiveIndicator E i y n)
          (sourceQuestionPositiveIndicator E i y 0) P P)
    (hpositive_mean :
      ∀ i : Fin L, ∀ y : Y,
        ∫ ω, sourceQuestionPositiveIndicator E i y 0 ω ∂P =
          H y * ψ (quality i) y)
    (hscore_integrable :
      ∀ i : Fin L, Integrable (sourceAggregatePositiveIndicator E i 0) P)
    (hscore_indep :
      ∀ i : Fin L,
        Pairwise ((· ⟂ᵢ[P] ·) on sourceAggregatePositiveIndicator E i))
    (hscore_ident :
      ∀ i : Fin L, ∀ n : ℕ,
        ProbabilityTheory.IdentDistrib
          (sourceAggregatePositiveIndicator E i n)
          (sourceAggregatePositiveIndicator E i 0) P P)
    (hscore_mean :
      ∀ i : Fin L,
        ∫ ω, sourceAggregatePositiveIndicator E i 0 ω ∂P =
          sourceExpectedAggregateScore ψ H (quality i))
    (hscore_strict :
      StrictMono (fun i : Fin L =>
        sourceExpectedAggregateScore ψ H (quality i))) :
    ∀ᵐ ω ∂P,
      TendstoUniformlyOn
        (fun N : ℕ => fun p : Fin L × Y =>
          sourceExperimentEmpiricalQuestionResponse E p.1 p.2 N ω)
        (fun p : Fin L × Y => ψ (quality p.1) p.2)
        atTop Set.univ ∧
      (∀ᶠ N : ℕ in atTop,
        StrictMono (fun i : Fin L =>
          sourceExperimentEmpiricalMean
            (sourceAggregatePositiveIndicator E i) N ω)) := by
  filter_upwards
    [lemmaB2_knownTypeExperiment_ae_question_response_of_iid
      P E quality ψ H hHpos hasked_integrable hasked_indep hasked_ident
        hasked_mean hpositive_integrable hpositive_indep hpositive_ident
        hpositive_mean,
      lemmaB3_unknownTypeExperiment_ae_eventual_true_order_of_iid
        P (sourceAggregatePositiveIndicator E)
          (fun i : Fin L => sourceExpectedAggregateScore ψ H (quality i))
          hscore_strict hscore_integrable hscore_indep hscore_ident
          hscore_mean] with ω hresponse hrank
  refine ⟨?_, hrank⟩
  exact
    lemmaB2_knownTypeExperiment_finite_representatives_uniform_of_pointwise
      (fun N i y => sourceExperimentEmpiricalQuestionResponse E i y N ω)
      (fun i y => ψ (quality i) y) hresponse

/--
Corrected stochastic core of Lemma B.3 for a fixed finite experiment: almost
sure uniform response learning and eventual recovery of the true item order
hold jointly under IID observations and strict score identifiability.
-/
theorem lemmaB3_unknownTypeExperiment_ae_response_and_rank_of_iid
    {Ω Y : Type*} {L : ℕ} [MeasurableSpace Ω] [Fintype Y]
    (P : Measure Ω)
    (quality expectedScore : Fin L → ℝ) (ψ : ℝ → Y → ℝ)
    (responseObservation : Fin L → Y → ℕ → Ω → ℝ)
    (scoreObservation : Fin L → ℕ → Ω → ℝ)
    (hresponse_integrable :
      ∀ i : Fin L, ∀ y : Y, Integrable (responseObservation i y 0) P)
    (hresponse_indep :
      ∀ i : Fin L, ∀ y : Y,
        Pairwise ((· ⟂ᵢ[P] ·) on responseObservation i y))
    (hresponse_ident :
      ∀ i : Fin L, ∀ y : Y, ∀ n : ℕ,
        ProbabilityTheory.IdentDistrib
          (responseObservation i y n) (responseObservation i y 0) P P)
    (hresponse_mean :
      ∀ i : Fin L, ∀ y : Y,
        ∫ ω, responseObservation i y 0 ω ∂P = ψ (quality i) y)
    (hscore_integrable :
      ∀ i : Fin L, Integrable (scoreObservation i 0) P)
    (hscore_indep :
      ∀ i : Fin L, Pairwise ((· ⟂ᵢ[P] ·) on scoreObservation i))
    (hscore_ident :
      ∀ i : Fin L, ∀ n : ℕ,
        ProbabilityTheory.IdentDistrib
          (scoreObservation i n) (scoreObservation i 0) P P)
    (hscore_mean :
      ∀ i : Fin L,
        ∫ ω, scoreObservation i 0 ω ∂P = expectedScore i)
    (hscore_strict : StrictMono expectedScore) :
    ∀ᵐ ω ∂P,
      TendstoUniformlyOn
        (fun N : ℕ => fun p : Fin L × Y =>
          sourceExperimentEmpiricalMean (responseObservation p.1 p.2) N ω)
        (fun p : Fin L × Y => ψ (quality p.1) p.2)
        atTop Set.univ ∧
      (∀ᶠ N : ℕ in atTop,
        StrictMono (fun i : Fin L =>
          sourceExperimentEmpiricalMean (scoreObservation i) N ω)) := by
  filter_upwards
    [lemmaB2_knownTypeExperiment_ae_finite_uniform_of_iid
      P quality ψ responseObservation hresponse_integrable hresponse_indep
        hresponse_ident hresponse_mean,
      lemmaB3_unknownTypeExperiment_ae_eventual_true_order_of_iid
        P scoreObservation expectedScore hscore_strict hscore_integrable
          hscore_indep hscore_ident hscore_mean] with ω hresponse hrank
  exact ⟨hresponse, hrank⟩

/-!
## The printed two-scale limits

Lemmas B.2 and B.3 first send the per-item sample count to infinity for a
fixed finite item set, and only then send the number of representative items
to infinity.  The next two deterministic lemmas record that iterated
quantifier order explicitly.  Using `Fin (L + 1)` avoids an empty item type at
the harmless initial index `L = 0`; thus the outer index represents `L + 1`
items.
-/

/--
Deterministic two-scale completion of Lemma B.2.  Fixed-item-count uniform
empirical convergence and a vanishing representative mesh imply the source's
iterated uniform limit: for every tolerance, all sufficiently fine item
meshes admit a (mesh-dependent) sample threshold after which every
item-question estimate is uniformly accurate.
-/
theorem lemmaB2_knownTypeExperiment_iterated_uniform_of_fixed_finite_uniform
    {Y : Type*} [Finite Y]
    (psiHat : (L : ℕ) → ℕ → Fin (L + 1) → Y → ℝ)
    (quality : (L : ℕ) → Fin (L + 1) → ℝ)
    (representative : (L : ℕ) → ℝ → Fin (L + 1))
    (psi : ℝ → Y → ℝ)
    (hfixed :
      ∀ L : ℕ,
        TendstoUniformlyOn
          (fun N : ℕ => fun p : Fin (L + 1) × Y =>
            psiHat L N p.1 p.2)
          (fun p : Fin (L + 1) × Y => psi (quality L p.1) p.2)
          atTop Set.univ)
    (hmesh :
      ∀ δ > 0,
        ∀ᶠ L : ℕ in atTop,
          ∀ θ ∈ Set.Icc (0 : ℝ) 1,
            dist (quality L (representative L θ)) θ < δ)
    {K : ℝ} (hK : 0 ≤ K)
    (hlipschitz :
      ∀ (θ θ' : ℝ) (y : Y),
        dist (psi θ y) (psi θ' y) ≤ K * dist θ θ') :
    ∀ ε > 0,
      ∀ᶠ L : ℕ in atTop,
        ∀ᶠ N : ℕ in atTop,
          ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ y : Y,
            dist (psiHat L N (representative L θ) y) (psi θ y) < ε := by
  letI := Fintype.ofFinite Y
  intro ε hε
  have hdenom : 0 < 2 * (K + 1) := by positivity
  have hδ : 0 < ε / (2 * (K + 1)) := div_pos hε hdenom
  filter_upwards [hmesh (ε / (2 * (K + 1))) hδ] with L hL
  have hfixedL :=
    (Metric.tendstoUniformlyOn_iff.mp (hfixed L)) (ε / 2) (by positivity)
  filter_upwards [hfixedL] with N hN
  intro θ hθ y
  have hemp :
      dist (psiHat L N (representative L θ) y)
          (psi (quality L (representative L θ)) y) < ε / 2 := by
    simpa [dist_comm] using
      hN (representative L θ, y) (Set.mem_univ _)
  have hmeshθ := hL θ hθ
  have hKlt :
      K * dist (quality L (representative L θ)) θ < ε / 2 := by
    have hKltK : K < K + 1 := by linarith
    have hnonneg : 0 ≤ dist (quality L (representative L θ)) θ :=
      dist_nonneg
    calc
      K * dist (quality L (representative L θ)) θ ≤
          (K + 1) * dist (quality L (representative L θ)) θ :=
            mul_le_mul_of_nonneg_right hKltK.le hnonneg
      _ < (K + 1) * (ε / (2 * (K + 1))) :=
        mul_lt_mul_of_pos_left hmeshθ (by linarith)
      _ = ε / 2 := by field_simp
  have hpsi :
      dist (psi (quality L (representative L θ)) y) (psi θ y) < ε / 2 :=
    lt_of_le_of_lt
      (hlipschitz (quality L (representative L θ)) θ y) hKlt
  calc
    dist (psiHat L N (representative L θ) y) (psi θ y) ≤
        dist (psiHat L N (representative L θ) y)
            (psi (quality L (representative L θ)) y) +
          dist (psi (quality L (representative L θ)) y) (psi θ y) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hemp hpsi
    _ = ε := by ring

/--
Deterministic two-scale completion of the corrected Lemma B.3.  In addition
to the iterated uniform response limit, the conclusion retains the source's
fixed-item-count eventual rank recovery.  Thus neither empirical tracking nor
ranking consistency is accepted as a final theorem premise.
-/
theorem lemmaB3_unknownTypeExperiment_iterated_uniform_and_rank_of_fixed_finite
    {Y : Type*} [Finite Y]
    (psiHat : (L : ℕ) → ℕ → Fin (L + 1) → Y → ℝ)
    (scoreHat : (L : ℕ) → ℕ → Fin (L + 1) → ℝ)
    (quality : (L : ℕ) → Fin (L + 1) → ℝ)
    (rankRepresentative : (L : ℕ) → ℝ → Fin (L + 1))
    (psi : ℝ → Y → ℝ)
    (hfixed :
      ∀ L : ℕ,
        TendstoUniformlyOn
            (fun N : ℕ => fun p : Fin (L + 1) × Y =>
              psiHat L N p.1 p.2)
            (fun p : Fin (L + 1) × Y => psi (quality L p.1) p.2)
            atTop Set.univ ∧
          (∀ᶠ N : ℕ in atTop, StrictMono (scoreHat L N)))
    (hmesh :
      ∀ δ > 0,
        ∀ᶠ L : ℕ in atTop,
          ∀ θ ∈ Set.Icc (0 : ℝ) 1,
            dist (quality L (rankRepresentative L θ)) θ < δ)
    {K : ℝ} (hK : 0 ≤ K)
    (hlipschitz :
      ∀ (θ θ' : ℝ) (y : Y),
        dist (psi θ y) (psi θ' y) ≤ K * dist θ θ') :
    ∀ ε > 0,
      ∀ᶠ L : ℕ in atTop,
        ∀ᶠ N : ℕ in atTop,
          StrictMono (scoreHat L N) ∧
            ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ y : Y,
              dist (psiHat L N (rankRepresentative L θ) y) (psi θ y) < ε := by
  intro ε hε
  have hresponse :
      ∀ᶠ L : ℕ in atTop,
        ∀ᶠ N : ℕ in atTop,
          ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ y : Y,
            dist (psiHat L N (rankRepresentative L θ) y) (psi θ y) < ε :=
    lemmaB2_knownTypeExperiment_iterated_uniform_of_fixed_finite_uniform
      psiHat quality rankRepresentative psi (fun L => (hfixed L).1)
      hmesh hK hlipschitz ε hε
  filter_upwards [hresponse] with L hresponseL
  filter_upwards [hresponseL, (hfixed L).2] with N hN hrank
  exact ⟨hrank, hN⟩

/--
Full source-shaped Lemma B.2 for the literal random-question experiment.
All empirical convergence is derived from the primitive IID observation
fields.  The conclusion preserves the printed order `N → ∞` for each fixed
finite experiment, followed by `L → ∞` for the representative mesh.
-/
theorem lemmaB2_knownTypeExperiment_ae_iterated_uniform_of_random_question_iid
    {Ω Y : Type*} [MeasurableSpace Ω]
    [Fintype Y] [DecidableEq Y]
    (P : Measure Ω)
    (E : (L : ℕ) → SourceRandomQuestionExperiment Ω (Fin (L + 1)) Y)
    (quality : (L : ℕ) → Fin (L + 1) → ℝ)
    (representative : (L : ℕ) → ℝ → Fin (L + 1))
    (psi : ℝ → Y → ℝ) (H : Y → ℝ)
    (hHpos : ∀ y : Y, 0 < H y)
    (hasked_integrable :
      ∀ L (i : Fin (L + 1)) (y : Y),
        Integrable (sourceQuestionAskedIndicator (E L) i y 0) P)
    (hasked_indep :
      ∀ L (i : Fin (L + 1)) (y : Y),
        Pairwise ((· ⟂ᵢ[P] ·) on sourceQuestionAskedIndicator (E L) i y))
    (hasked_ident :
      ∀ L (i : Fin (L + 1)) (y : Y) (n : ℕ),
        ProbabilityTheory.IdentDistrib
          (sourceQuestionAskedIndicator (E L) i y n)
          (sourceQuestionAskedIndicator (E L) i y 0) P P)
    (hasked_mean :
      ∀ L (i : Fin (L + 1)) (y : Y),
        ∫ ω, sourceQuestionAskedIndicator (E L) i y 0 ω ∂P = H y)
    (hpositive_integrable :
      ∀ L (i : Fin (L + 1)) (y : Y),
        Integrable (sourceQuestionPositiveIndicator (E L) i y 0) P)
    (hpositive_indep :
      ∀ L (i : Fin (L + 1)) (y : Y),
        Pairwise ((· ⟂ᵢ[P] ·) on sourceQuestionPositiveIndicator (E L) i y))
    (hpositive_ident :
      ∀ L (i : Fin (L + 1)) (y : Y) (n : ℕ),
        ProbabilityTheory.IdentDistrib
          (sourceQuestionPositiveIndicator (E L) i y n)
          (sourceQuestionPositiveIndicator (E L) i y 0) P P)
    (hpositive_mean :
      ∀ L (i : Fin (L + 1)) (y : Y),
        ∫ ω, sourceQuestionPositiveIndicator (E L) i y 0 ω ∂P =
          H y * psi (quality L i) y)
    (hmesh :
      ∀ δ > 0,
        ∀ᶠ L : ℕ in atTop,
          ∀ θ ∈ Set.Icc (0 : ℝ) 1,
            dist (quality L (representative L θ)) θ < δ)
    {K : ℝ} (hK : 0 ≤ K)
    (hlipschitz :
      ∀ (θ θ' : ℝ) (y : Y),
        dist (psi θ y) (psi θ' y) ≤ K * dist θ θ') :
    ∀ᵐ ω ∂P,
      ∀ ε > 0,
        ∀ᶠ L : ℕ in atTop,
          ∀ᶠ N : ℕ in atTop,
            ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ y : Y,
              dist
                  (sourceExperimentEmpiricalQuestionResponse
                    (E L) (representative L θ) y N ω)
                  (psi θ y) < ε := by
  have hfixed :
      ∀ᵐ ω ∂P, ∀ L : ℕ,
        TendstoUniformlyOn
          (fun N : ℕ => fun p : Fin (L + 1) × Y =>
            sourceExperimentEmpiricalQuestionResponse (E L) p.1 p.2 N ω)
          (fun p : Fin (L + 1) × Y => psi (quality L p.1) p.2)
          atTop Set.univ := by
    rw [ae_all_iff]
    intro L
    filter_upwards
      [lemmaB2_knownTypeExperiment_ae_question_response_of_iid
        P (E L) (quality L) psi H hHpos
        (hasked_integrable L) (hasked_indep L) (hasked_ident L)
        (hasked_mean L) (hpositive_integrable L) (hpositive_indep L)
        (hpositive_ident L) (hpositive_mean L)] with ω hω
    exact
      lemmaB2_knownTypeExperiment_finite_representatives_uniform_of_pointwise
        (fun N i y =>
          sourceExperimentEmpiricalQuestionResponse (E L) i y N ω)
        (fun i y => psi (quality L i) y) hω
  filter_upwards [hfixed] with ω hω
  exact
    lemmaB2_knownTypeExperiment_iterated_uniform_of_fixed_finite_uniform
      (fun L N i y =>
        sourceExperimentEmpiricalQuestionResponse (E L) i y N ω)
      quality representative psi hω hmesh hK hlipschitz

/--
Full corrected source-shaped Lemma B.3 for the literal random-question
experiment.  Response tracking and empirical rank recovery are both derived
from primitive IID fields, while strict aggregate-score identifiability is
the explicit minor assumption needed by the printed ranking argument.
-/
theorem lemmaB3_unknownTypeExperiment_ae_iterated_uniform_and_rank_of_random_question_iid
    {Ω Y : Type*} [MeasurableSpace Ω]
    [Fintype Y] [DecidableEq Y]
    (P : Measure Ω)
    (E : (L : ℕ) → SourceRandomQuestionExperiment Ω (Fin (L + 1)) Y)
    (quality : (L : ℕ) → Fin (L + 1) → ℝ)
    (rankRepresentative : (L : ℕ) → ℝ → Fin (L + 1))
    (psi : ℝ → Y → ℝ) (H : Y → ℝ)
    (hHpos : ∀ y : Y, 0 < H y)
    (hasked_integrable :
      ∀ L (i : Fin (L + 1)) (y : Y),
        Integrable (sourceQuestionAskedIndicator (E L) i y 0) P)
    (hasked_indep :
      ∀ L (i : Fin (L + 1)) (y : Y),
        Pairwise ((· ⟂ᵢ[P] ·) on sourceQuestionAskedIndicator (E L) i y))
    (hasked_ident :
      ∀ L (i : Fin (L + 1)) (y : Y) (n : ℕ),
        ProbabilityTheory.IdentDistrib
          (sourceQuestionAskedIndicator (E L) i y n)
          (sourceQuestionAskedIndicator (E L) i y 0) P P)
    (hasked_mean :
      ∀ L (i : Fin (L + 1)) (y : Y),
        ∫ ω, sourceQuestionAskedIndicator (E L) i y 0 ω ∂P = H y)
    (hpositive_integrable :
      ∀ L (i : Fin (L + 1)) (y : Y),
        Integrable (sourceQuestionPositiveIndicator (E L) i y 0) P)
    (hpositive_indep :
      ∀ L (i : Fin (L + 1)) (y : Y),
        Pairwise ((· ⟂ᵢ[P] ·) on sourceQuestionPositiveIndicator (E L) i y))
    (hpositive_ident :
      ∀ L (i : Fin (L + 1)) (y : Y) (n : ℕ),
        ProbabilityTheory.IdentDistrib
          (sourceQuestionPositiveIndicator (E L) i y n)
          (sourceQuestionPositiveIndicator (E L) i y 0) P P)
    (hpositive_mean :
      ∀ L (i : Fin (L + 1)) (y : Y),
        ∫ ω, sourceQuestionPositiveIndicator (E L) i y 0 ω ∂P =
          H y * psi (quality L i) y)
    (hscore_integrable :
      ∀ L (i : Fin (L + 1)),
        Integrable (sourceAggregatePositiveIndicator (E L) i 0) P)
    (hscore_indep :
      ∀ L (i : Fin (L + 1)),
        Pairwise ((· ⟂ᵢ[P] ·) on sourceAggregatePositiveIndicator (E L) i))
    (hscore_ident :
      ∀ L (i : Fin (L + 1)) (n : ℕ),
        ProbabilityTheory.IdentDistrib
          (sourceAggregatePositiveIndicator (E L) i n)
          (sourceAggregatePositiveIndicator (E L) i 0) P P)
    (hscore_mean :
      ∀ L (i : Fin (L + 1)),
        ∫ ω, sourceAggregatePositiveIndicator (E L) i 0 ω ∂P =
          sourceExpectedAggregateScore psi H (quality L i))
    (hscore_strict :
      ∀ L : ℕ,
        StrictMono (fun i : Fin (L + 1) =>
          sourceExpectedAggregateScore psi H (quality L i)))
    (hmesh :
      ∀ δ > 0,
        ∀ᶠ L : ℕ in atTop,
          ∀ θ ∈ Set.Icc (0 : ℝ) 1,
            dist (quality L (rankRepresentative L θ)) θ < δ)
    {K : ℝ} (hK : 0 ≤ K)
    (hlipschitz :
      ∀ (θ θ' : ℝ) (y : Y),
        dist (psi θ y) (psi θ' y) ≤ K * dist θ θ') :
    ∀ᵐ ω ∂P,
      ∀ ε > 0,
        ∀ᶠ L : ℕ in atTop,
          ∀ᶠ N : ℕ in atTop,
            StrictMono (fun i : Fin (L + 1) =>
              sourceExperimentEmpiricalMean
                (sourceAggregatePositiveIndicator (E L) i) N ω) ∧
              ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ y : Y,
                dist
                    (sourceExperimentEmpiricalQuestionResponse
                      (E L) (rankRepresentative L θ) y N ω)
                    (psi θ y) < ε := by
  have hfixed :
      ∀ᵐ ω ∂P, ∀ L : ℕ,
        TendstoUniformlyOn
            (fun N : ℕ => fun p : Fin (L + 1) × Y =>
              sourceExperimentEmpiricalQuestionResponse (E L) p.1 p.2 N ω)
            (fun p : Fin (L + 1) × Y => psi (quality L p.1) p.2)
            atTop Set.univ ∧
          (∀ᶠ N : ℕ in atTop,
            StrictMono (fun i : Fin (L + 1) =>
              sourceExperimentEmpiricalMean
                (sourceAggregatePositiveIndicator (E L) i) N ω)) := by
    rw [ae_all_iff]
    intro L
    exact
      lemmaB3_unknownTypeExperiment_ae_random_question_response_and_rank_of_iid
        P (E L) (quality L) psi H hHpos
        (hasked_integrable L) (hasked_indep L) (hasked_ident L)
        (hasked_mean L) (hpositive_integrable L) (hpositive_indep L)
        (hpositive_ident L) (hpositive_mean L)
        (hscore_integrable L) (hscore_indep L) (hscore_ident L)
        (hscore_mean L) (hscore_strict L)
  filter_upwards [hfixed] with ω hω
  exact
    lemmaB3_unknownTypeExperiment_iterated_uniform_and_rank_of_fixed_finite
      (fun L N i y =>
        sourceExperimentEmpiricalQuestionResponse (E L) i y N ω)
      (fun L N i =>
        sourceExperimentEmpiricalMean
          (sourceAggregatePositiveIndicator (E L) i) N ω)
      quality rankRepresentative psi hω hmesh hK hlipschitz

end

end GJ19OptimalBinaryRatingSystems
