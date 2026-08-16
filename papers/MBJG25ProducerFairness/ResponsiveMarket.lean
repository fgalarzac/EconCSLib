import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import EconCSLib.Foundations.Econometrics.RatingModels.BinaryRating
import EconCSLib.Foundations.Probability.FinsetVariance
import EconCSLib.Foundations.Probability.FiniteExpectation

namespace MBJG25ProducerFairness
namespace Responsive

/--
Selection Rate (SR) for a product $v$.
Defined in the responsive market section as the expected number of times selected
divided by its lifespan. We parameterize this directly.
-/
noncomputable def selectionRate (selections : ℝ) (lifespan : ℝ) : ℝ :=
  selections / lifespan

/--
Individual Producer Unfairness.
Defined as the standard deviation in Selection Rate (SR) among producers with
the same true quality `q`. The source leaves the finite-sample divisor implicit;
`finsetVariance` uses the empirical-distribution (`1 / |S|`) convention.
-/
noncomputable def producerUnfairnessVariance
    {V : Type*} [Fintype V] [DecidableEq V]
    (selections : V → ℝ)
    (lifespan : V → ℝ)
    (q_v : V → ℝ)
    (q : ℝ) : ℝ :=
  let S := Finset.univ.filter (fun v => q_v v = q)
  EconCSLib.Statistics.finsetVariance S (fun v => selectionRate (selections v) (lifespan v))

/--
Individual Producer Unfairness.
The standard deviation counterpart.
-/
noncomputable def producerUnfairness
    {V : Type*} [Fintype V] [DecidableEq V]
    (selections : V → ℝ)
    (lifespan : V → ℝ)
    (q_v : V → ℝ)
    (q : ℝ) : ℝ :=
  Real.sqrt (producerUnfairnessVariance selections lifespan q_v q)

/-- Finite bias--variance decomposition for one conditional rating law. -/
theorem finite_bias_variance_decomposition
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μ : PMF Ω) (X : Ω → ℝ) (q : ℝ) :
    EconCSLib.pmfExp μ (fun ω => (X ω - q) ^ 2) =
      (EconCSLib.pmfExp μ X - q) ^ 2 +
        EconCSLib.pmfExp μ (fun ω =>
          (X ω - EconCSLib.pmfExp μ X) ^ 2) := by
  let mean := EconCSLib.pmfExp μ X
  have hpoint :
      (fun ω => (X ω - q) ^ 2) =
        (fun ω =>
          (X ω - mean) ^ 2 +
            (2 * (mean - q)) * (X ω - mean) + (mean - q) ^ 2) := by
    funext ω
    ring
  rw [hpoint, EconCSLib.pmfExp_add, EconCSLib.pmfExp_add,
    EconCSLib.pmfExp_const_mul, EconCSLib.pmfExp_sub,
    EconCSLib.pmfExp_const, EconCSLib.pmfExp_const]
  change _ = (mean - q) ^ 2 + _
  ring

/--
Mean Squared Error (MSE) decomposition in the responsive setting.
As shown in Appendix C, when the number of reviews $N$ is a random variable,
the expected MSE conditional on true quality $q_v$ decomposes into the expected
squared bias and the expected variance over the random variable $N$.
-/
theorem paper_responsive_mse_decomposition
    {α Ω : Type*} [Fintype α] [DecidableEq α]
    [Fintype Ω] [DecidableEq Ω]
    {alpha beta eta q_v : ℝ}
    (state_dist : PMF α)
    (rating_dist : α → PMF Ω)
    (N : α → ℝ)
    (posterior_rating : α → Ω → ℝ)
    (h_cond_mean : ∀ s,
      EconCSLib.pmfExp (rating_dist s) (posterior_rating s) =
      EconCSLib.Statistics.priorWeightedPosteriorMean alpha beta eta (N s) q_v)
    (h_cond_var : ∀ s,
      EconCSLib.pmfExp (rating_dist s) (fun ω =>
        (posterior_rating s ω -
          EconCSLib.pmfExp (rating_dist s) (posterior_rating s)) ^ 2) =
      EconCSLib.Statistics.priorWeightedVariance alpha beta eta (N s) q_v) :
    EconCSLib.pmfExp state_dist (fun s =>
      EconCSLib.pmfExp (rating_dist s) (fun ω =>
        (posterior_rating s ω - q_v) ^ 2)) =
      EconCSLib.pmfExp state_dist (fun s =>
        EconCSLib.Statistics.priorWeightedSquaredBias alpha beta eta (N s) q_v) +
      EconCSLib.pmfExp state_dist (fun s =>
        EconCSLib.Statistics.priorWeightedVariance alpha beta eta (N s) q_v) := by
  have h_eq : ∀ s,
      EconCSLib.pmfExp (rating_dist s) (fun ω =>
        (posterior_rating s ω - q_v) ^ 2) =
      EconCSLib.Statistics.priorWeightedSquaredBias alpha beta eta (N s) q_v +
      EconCSLib.Statistics.priorWeightedVariance alpha beta eta (N s) q_v := by
    intro s
    have h := finite_bias_variance_decomposition
      (rating_dist s) (posterior_rating s) q_v
    rw [h_cond_var s, h_cond_mean s] at h
    simpa [EconCSLib.Statistics.priorWeightedSquaredBias,
      EconCSLib.Statistics.priorWeightedBias] using h
  simp only [h_eq]
  exact EconCSLib.pmfExp_add state_dist _ _

end Responsive
end MBJG25ProducerFairness
