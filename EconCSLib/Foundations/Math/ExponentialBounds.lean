import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Elementary Exponential Bounds

Reusable real exponential inequalities for finite probability estimates.

## Main declarations

- `exp_neg_two_div_le_one_sub_inv_of_two_le`: for `x >= 2`,
  `exp(-(2/x)) <= 1 - 1/x`.
- `exp_neg_two_mul_nat_div_le_one_sub_inv_pow_of_two_le`: the corresponding
  finite-power lower bound.
- `log_add_div_self_le_div`: the shifted logarithm bound
  `log ((x + δ) / x) <= δ / x`.
- `le_neg_log_one_sub`: the standard bound `x <= -log (1 - x)` on
  `[0, 1)`.
- `neg_log_one_sub_le_div_self`: the standard upper bound
  `-log (1 - x) <= x / (1 - x)` on `[0, 1)`.
- `neg_log_one_add_sqrt_div_two_ge_one_fifth_neg_log`: a one-variable
  endpoint-refinement logarithmic bound used in rate-doubling arguments.
- `half_mul_le_one_sub_exp_neg_of_mem_Icc`: a linear lower bound for
  `1 - exp (-x)` on `[0, 1]`.
- `mul_delta_split_budget_eq_of_delta_eq_div_mul_add`: algebra for choosing
  a grid width from a two-term error budget.
-/

namespace EconCSLib
namespace Math

/-- Exponentiating half a logarithm gives the positive square root. -/
theorem exp_log_div_two_eq_sqrt {x : ℝ} (hx : 0 < x) :
    Real.exp (Real.log x / 2) = Real.sqrt x := by
  rw [← Real.log_sqrt hx.le]
  exact Real.exp_log (Real.sqrt_pos.mpr hx)

/--
For `0 ≤ x < 1`, the logarithmic penalty from `1 - x^2` is no larger than
the penalty from `1 - x`.
-/
theorem neg_log_one_sub_sq_le_neg_log_one_sub
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    -Real.log (1 - x ^ 2) ≤ -Real.log (1 - x) := by
  have hx_sq_le : x ^ 2 ≤ x := by
    nlinarith [mul_self_le_mul_self hx0 hx1.le]
  have harg_left_pos : 0 < 1 - x := by linarith
  have harg_right_pos : 0 < 1 - x ^ 2 := by
    have hx_sq_lt : x ^ 2 < 1 := (sq_lt_one_iff₀ hx0).mpr hx1
    linarith
  have harg_le : 1 - x ≤ 1 - x ^ 2 := by linarith
  have hlog_le :
      Real.log (1 - x) ≤ Real.log (1 - x ^ 2) :=
    Real.log_le_log harg_left_pos harg_le
  linarith

/-- For `0 ≤ x < 1`, `x ≤ -log (1 - x)`. -/
theorem le_neg_log_one_sub
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    x ≤ -Real.log (1 - x) := by
  have hpos : 0 < 1 - x := by linarith
  have hlog := Real.log_le_sub_one_of_pos hpos
  linarith

/-- For `0 ≤ x < 1`, `-log (1 - x) ≤ x / (1 - x)`. -/
theorem neg_log_one_sub_le_div_self
    {x : ℝ} (_hx0 : 0 ≤ x) (hx1 : x < 1) :
    -Real.log (1 - x) ≤ x / (1 - x) := by
  have hpos : 0 < 1 - x := by linarith
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at hlog
  have hsub : (1 - x)⁻¹ - 1 = x / (1 - x) := by
    field_simp [ne_of_gt hpos]
    ring
  simpa [hsub] using hlog

/-- The map `x ↦ -log (1 - x)` is monotone on `(-∞, 1)`. -/
theorem neg_log_one_sub_mono
    {x y : ℝ} (hxy : x ≤ y) (hy1 : y < 1) :
    -Real.log (1 - x) ≤ -Real.log (1 - y) := by
  have hy_pos : 0 < 1 - y := by linarith
  have harg_le : 1 - y ≤ 1 - x := by linarith
  have hlog_le :
      Real.log (1 - y) ≤ Real.log (1 - x) :=
    Real.log_le_log hy_pos harg_le
  linarith

/--
The map `x ↦ -log (1 - x^2)` is monotone on `[0, 1)`.
-/
theorem neg_log_one_sub_sq_mono
    {x y : ℝ} (hx0 : 0 ≤ x) (hxy : x ≤ y) (hy1 : y < 1) :
    -Real.log (1 - x ^ 2) ≤ -Real.log (1 - y ^ 2) := by
  have hy0 : 0 ≤ y := le_trans hx0 hxy
  have hx1 : x < 1 := lt_of_le_of_lt hxy hy1
  have hx_sq_lt : x ^ 2 < 1 := (sq_lt_one_iff₀ hx0).mpr hx1
  have hy_sq_lt : y ^ 2 < 1 := (sq_lt_one_iff₀ hy0).mpr hy1
  have hsq_le : x ^ 2 ≤ y ^ 2 :=
    by simpa [pow_two] using mul_self_le_mul_self hx0 hxy
  have harg_pos : 0 < 1 - y ^ 2 := by linarith
  have harg_le : 1 - y ^ 2 ≤ 1 - x ^ 2 := by linarith
  have hlog_le :
      Real.log (1 - y ^ 2) ≤ Real.log (1 - x ^ 2) :=
    Real.log_le_log harg_pos harg_le
  linarith

/-- For `0 < x < 1`, the squared endpoint logarithmic penalty is positive. -/
theorem neg_log_one_sub_sq_pos
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < -Real.log (1 - x ^ 2) := by
  have hx_sq_pos : 0 < x ^ 2 := sq_pos_of_ne_zero (ne_of_gt hx0)
  have hx_sq_lt : x ^ 2 < 1 := (sq_lt_one_iff₀ hx0.le).mpr hx1
  have harg_pos : 0 < 1 - x ^ 2 := by linarith
  have harg_lt_one : 1 - x ^ 2 < 1 := by linarith
  have hlog_neg : Real.log (1 - x ^ 2) < 0 :=
    Real.log_neg harg_pos harg_lt_one
  linarith

/--
For any real denominator at least two, the elementary logarithmic estimate
`log(1 - 1/x) >= -2/x` gives `exp(-2/x) <= 1 - 1/x`.
-/
theorem exp_neg_two_div_le_one_sub_inv_of_two_le
    {x : ℝ} (hx : 2 ≤ x) :
    Real.exp (-(2 / x)) ≤ 1 - 1 / x := by
  have hx_pos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hxm1_pos : 0 < x - 1 := by linarith
  have hy_pos : 0 < 1 - 1 / x := by
    rw [sub_pos]
    rw [div_lt_one hx_pos]
    linarith
  have hrepr :
      1 - 1 / x = (1 + 1 / (x - 1))⁻¹ := by
    field_simp [ne_of_gt hx_pos, ne_of_gt hxm1_pos]
    ring
  have hlog_upper :
      Real.log (1 + 1 / (x - 1)) ≤ 2 / x := by
    have harg_pos : 0 < 1 + 1 / (x - 1) := by positivity
    have hlog_le :
        Real.log (1 + 1 / (x - 1)) ≤
          (1 + 1 / (x - 1)) - 1 :=
      Real.log_le_sub_one_of_pos harg_pos
    have hfrac : 1 / (x - 1) ≤ 2 / x := by
      rw [div_le_div_iff₀ hxm1_pos hx_pos]
      nlinarith
    linarith
  have hlog_lower :
      -(2 / x) ≤ Real.log (1 - 1 / x) := by
    rw [hrepr, Real.log_inv]
    exact neg_le_neg hlog_upper
  exact (Real.le_log_iff_exp_le hy_pos).mp hlog_lower

/--
Finite-power form of `exp_neg_two_div_le_one_sub_inv_of_two_le`: if `x >= 2`,
then `exp(-(2N/x)) <= (1 - 1/x)^N`.
-/
theorem exp_neg_two_mul_nat_div_le_one_sub_inv_pow_of_two_le
    (N : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    Real.exp (-(2 * (N : ℝ) / x)) ≤ (1 - 1 / x) ^ N := by
  have hbase := exp_neg_two_div_le_one_sub_inv_of_two_le (x := x) hx
  have hpow :
      (Real.exp (-(2 / x))) ^ N ≤ (1 - 1 / x) ^ N :=
    pow_le_pow_left₀ (Real.exp_pos _).le hbase N
  have hleft :
      Real.exp (-(2 * (N : ℝ) / x)) =
        (Real.exp (-(2 / x))) ^ N := by
    calc
      Real.exp (-(2 * (N : ℝ) / x)) =
          Real.exp ((N : ℝ) * (-(2 / x))) := by
            congr 1
            ring
      _ = (Real.exp (-(2 / x))) ^ N :=
          Real.exp_nat_mul (-(2 / x)) N
  simpa [hleft] using hpow

/--
Elementary shifted-log bound used in bisection approximation arguments:
`log ((x + δ) / x) ≤ δ / x` for a positive base point and nonnegative shift.
-/
theorem log_add_div_self_le_div {x δ : ℝ}
    (hx : 0 < x) (hδ : 0 ≤ δ) :
    Real.log ((x + δ) / x) ≤ δ / x := by
  have hnum_pos : 0 < x + δ := by linarith
  have harg_pos : 0 < (x + δ) / x := div_pos hnum_pos hx
  have hlog :
      Real.log ((x + δ) / x) ≤ (x + δ) / x - 1 :=
    Real.log_le_sub_one_of_pos harg_pos
  have hsub : (x + δ) / x - 1 = δ / x := by
    field_simp [ne_of_gt hx]
    ring
  simpa [hsub] using hlog

/--
Scaled shifted-log bound for nonnegative coefficients.
-/
theorem mul_log_add_div_self_le_mul_div {g x δ : ℝ}
    (hg : 0 ≤ g) (hx : 0 < x) (hδ : 0 ≤ δ) :
    g * Real.log ((x + δ) / x) ≤ g * (δ / x) :=
  mul_le_mul_of_nonneg_left (log_add_div_self_le_div hx hδ) hg

/--
For a nonnegative shift, the multiplicative shifted-log loss
`log ((x + δ) / x)` is antitone in the positive base point.
-/
theorem log_add_div_self_le_log_add_div_self_of_le
    {x y δ : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hδ : 0 ≤ δ) :
    Real.log ((y + δ) / y) ≤ Real.log ((x + δ) / x) := by
  have hy : 0 < y := hx.trans_le hxy
  have harg_y_pos : 0 < (y + δ) / y := by
    exact div_pos (by linarith) hy
  have hratio :
      (y + δ) / y ≤ (x + δ) / x := by
    have hdiv : δ / y ≤ δ / x :=
      div_le_div_of_nonneg_left hδ hx hxy
    have hy_ne : y ≠ 0 := ne_of_gt hy
    have hx_ne : x ≠ 0 := ne_of_gt hx
    rw [add_div, add_div, div_self hy_ne, div_self hx_ne]
    linarith
  exact Real.log_le_log harg_y_pos hratio

/--
For `t ∈ [1/2, 1]`, the endpoint refinement midpoint
`(1 + sqrt t) / 2` is at most the fifth root of `t`.

The proof is algebraic after setting `s = sqrt t`:
`32 s^2 - (1+s)^5 = (1-s)(s^4 + 6s^3 + 16s^2 - 6s - 1)`, and the last
factor is nonnegative for `s >= 1/2`.
-/
theorem one_add_sqrt_div_two_pow_five_le_self_of_half_le_of_le_one
    {t : ℝ} (hhalf : (1 / 2 : ℝ) ≤ t) (ht1 : t ≤ 1) :
    ((1 + Real.sqrt t) / 2) ^ 5 ≤ t := by
  have ht_nonneg : 0 ≤ t := by nlinarith
  let s : ℝ := Real.sqrt t
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg t
  have hs_sq : s ^ 2 = t := by
    dsimp [s]
    exact Real.sq_sqrt ht_nonneg
  have hs_le_one : s ≤ 1 := by
    have hs_sq_le : s ^ 2 ≤ (1 : ℝ) ^ 2 := by
      simpa [hs_sq] using ht1
    exact le_of_sq_le_sq hs_sq_le (by norm_num)
  have hs_ge_half : (1 / 2 : ℝ) ≤ s := by
    have hsq : ((1 / 2 : ℝ) ^ 2) ≤ s ^ 2 := by
      rw [hs_sq]
      norm_num
      nlinarith
    have habs : |(1 / 2 : ℝ)| ≤ |s| := by
      exact (sq_le_sq.mp hsq)
    simpa [abs_of_nonneg hs_nonneg] using habs
  have hmain_nonneg : 0 ≤ 16 * s ^ 2 - 6 * s - 1 := by
    have hleft : 0 ≤ 2 * s - 1 := by nlinarith
    have hright : 0 ≤ 8 * s + 1 := by nlinarith
    have hprod : 0 ≤ (2 * s - 1) * (8 * s + 1) :=
      mul_nonneg hleft hright
    have hprod_eq :
        (2 * s - 1) * (8 * s + 1) = 16 * s ^ 2 - 6 * s - 1 := by
      ring
    simpa [hprod_eq] using hprod
  have hs3_nonneg : 0 ≤ s ^ 3 := by positivity
  have hs4_nonneg : 0 ≤ s ^ 4 := by positivity
  have hfactor_nonneg :
      0 ≤ s ^ 4 + 6 * s ^ 3 + 16 * s ^ 2 - 6 * s - 1 := by
    nlinarith
  have hgap_nonneg :
      0 ≤ 32 * s ^ 2 - (1 + s) ^ 5 := by
    have hone_minus_nonneg : 0 ≤ 1 - s := by linarith
    have hprod_nonneg :
        0 ≤ (1 - s) *
          (s ^ 4 + 6 * s ^ 3 + 16 * s ^ 2 - 6 * s - 1) :=
      mul_nonneg hone_minus_nonneg hfactor_nonneg
    have hfactor :
        (1 - s) * (s ^ 4 + 6 * s ^ 3 + 16 * s ^ 2 - 6 * s - 1) =
          32 * s ^ 2 - (1 + s) ^ 5 := by
      ring
    simpa [hfactor] using hprod_nonneg
  have hpow :
      ((1 + s) / 2) ^ 5 ≤ s ^ 2 := by
    rw [div_pow]
    norm_num
    nlinarith
  simpa [s, hs_sq] using hpow

/--
For `t ∈ [1/2, 1]`, replacing the endpoint `t` by `(1 + sqrt t) / 2`
loses at most a factor `5` in the negative logarithmic rate.
-/
theorem neg_log_one_add_sqrt_div_two_ge_one_fifth_neg_log
    {t : ℝ} (hhalf : (1 / 2 : ℝ) ≤ t) (ht1 : t ≤ 1) :
    (1 / 5 : ℝ) * (-Real.log t) ≤
      -Real.log ((1 + Real.sqrt t) / 2) := by
  have ht_pos : 0 < t := by nlinarith
  have hbase_pos : 0 < (1 + Real.sqrt t) / 2 := by
    positivity
  have hpow :=
    one_add_sqrt_div_two_pow_five_le_self_of_half_le_of_le_one
      (t := t) hhalf ht1
  have hlog :
      Real.log (((1 + Real.sqrt t) / 2) ^ 5) ≤ Real.log t :=
    Real.log_le_log (pow_pos hbase_pos 5) hpow
  rw [Real.log_pow] at hlog
  norm_num at hlog
  nlinarith

/--
For `x ∈ [0, 1]`, the survival increment `1 - exp (-x)` is bounded below by
`x / 2`.
-/
theorem half_mul_le_one_sub_exp_neg_of_mem_Icc
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 2 ≤ 1 - Real.exp (-x) := by
  by_cases hx_zero : x = 0
  · subst x
    simp
  have hx_pos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx_zero)
  have hy : 2 ≤ 2 / x := by
    rw [le_div_iff₀ hx_pos]
    nlinarith
  have hbound :=
    exp_neg_two_div_le_one_sub_inv_of_two_le (x := 2 / x) hy
  have hrepr :
      Real.exp (-(2 / (2 / x))) = Real.exp (-x) := by
    congr 1
    field_simp [ne_of_gt hx_pos]
  have hrhs :
      1 - 1 / (2 / x) = 1 - x / 2 := by
    field_simp [ne_of_gt hx_pos]
  have hexp : Real.exp (-x) ≤ 1 - x / 2 := by
    simpa [hrepr, hrhs] using hbound
  linarith

/--
If `lower ≤ r` and `lower ∈ [0, 1]`, then a first-level endpoint of the form
`1 - exp (-r)` is at least `lower / 2`.
-/
theorem half_lower_le_one_sub_exp_neg_of_lower_le_rate
    {lower r : ℝ}
    (hlower0 : 0 ≤ lower) (hlower1 : lower ≤ 1)
    (hlower_le_rate : lower ≤ r) :
    lower / 2 ≤ 1 - Real.exp (-r) := by
  have hlinear :=
    half_mul_le_one_sub_exp_neg_of_mem_Icc hlower0 hlower1
  have hexp_mono : Real.exp (-r) ≤ Real.exp (-lower) :=
    Real.exp_le_exp.mpr (by linarith)
  have htail : 1 - Real.exp (-lower) ≤ 1 - Real.exp (-r) := by
    linarith
  exact hlinear.trans htail

/--
Elementary algebra for approximation proofs: if
`delta = eps / (g * (A + B))`, then the two weighted error-budget terms add
exactly to `eps`.
-/
theorem mul_delta_split_budget_eq_of_delta_eq_div_mul_add
    {g A B eps delta : ℝ}
    (hg : g ≠ 0)
    (hsum : A + B ≠ 0)
    (hdelta : delta = eps / (g * (A + B))) :
    g * (delta * A) + g * (delta * B) = eps := by
  subst delta
  field_simp [hg, hsum]

end Math
end EconCSLib
