import EconCSLib.Foundations.Probability.PoissonProcess

/-!
# Elementary Poisson moments

Low-level moment identities for Mathlib's `poissonMeasure`.  These belong
below any particular Poisson-process construction so forward, Palm, and
equilibrium models can all use the same integrability and expectation facts.
-/

namespace EconCSLib
namespace Probability
namespace PoissonProcess

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/-- The first moment of the real Poisson mass series. -/
theorem hasSum_poisson_firstMoment (x : ℝ) :
    HasSum (fun n : ℕ =>
      Real.exp (-x) * x ^ n / (n.factorial : ℝ) * n) x := by
  have hbase : HasSum (fun n : ℕ => Real.exp (-x) * x ^ n / (n.factorial : ℝ)) 1 := by
    convert (NormedSpace.expSeries_div_hasSum_exp x).mul_left (Real.exp (-x)) using 1
    · simp_rw [mul_div_assoc]
    · rw [← Real.exp_eq_exp_ℝ]
      rw [← Real.exp_add]
      ring_nf
      norm_num
  have hshift : HasSum (fun n : ℕ =>
      x * (Real.exp (-x) * x ^ n / (n.factorial : ℝ))) x := by
    simpa using hbase.mul_left x
  refine (hasSum_nat_add_iff' 1).mp ?_
  convert hshift.congr_fun (fun n => ?_) using 1 <;> simp
  field_simp
  simp only [Nat.factorial_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  ring

/-- A Poisson count has an integrable real-valued first moment. -/
theorem integrable_natCast_poissonMeasure (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)) (ProbabilityTheory.poissonMeasure r) := by
  rw [ProbabilityTheory.integrable_poissonMeasure_iff]
  simpa [Real.norm_eq_abs, abs_of_nonneg] using
    (hasSum_poisson_firstMoment (r : ℝ)).summable

/-- The real expectation of a Poisson random variable is its parameter. -/
theorem integral_id_poissonMeasure (r : ℝ≥0) :
    ∫ n : ℕ, (n : ℝ) ∂ProbabilityTheory.poissonMeasure r = r := by
  rw [ProbabilityTheory.integral_poissonMeasure]
  simpa [smul_eq_mul] using (hasSum_poisson_firstMoment (r : ℝ)).tsum_eq

end

end PoissonProcess
end Probability
end EconCSLib
