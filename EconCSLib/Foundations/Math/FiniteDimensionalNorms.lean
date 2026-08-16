import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic

/-!
# Finite-Coordinate Norm Formulas

Paper-neutral formulas for the finite-coordinate `L1`, `L2`, `L∞`, and finite
`Lp` quantities that occur in continuous-space voting and optimization models.
Deep normed-space and differentiability facts should live in later analysis
modules; this file keeps the finite sums explicit.
-/

open scoped BigOperators

namespace EconCSLib
namespace FiniteDimensionalNorms

noncomputable section

/-- Finite-coordinate `L1` quantity, written as a sum of absolute values. -/
def l1 {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  ∑ i : ι, |x i|

/-- Squared finite-coordinate `L2` quantity. -/
def l2Sq {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  ∑ i : ι, x i ^ 2

/-- Finite-coordinate Euclidean dot product, written as an explicit sum. -/
def dot {ι : Type*} [Fintype ι] (x y : ι → ℝ) : ℝ :=
  ∑ i : ι, x i * y i

/-- Finite-coordinate `L2` quantity, written as the square root of `l2Sq`. -/
def l2 {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  Real.sqrt (l2Sq x)

/-- Finite-coordinate `L∞` quantity, written as the maximum absolute coordinate. -/
def linf {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) : ℝ :=
  (Finset.univ : Finset ι).sup' Finset.univ_nonempty (fun i => |x i|)

/-- Finite-coordinate `Lp` power sum, `sum_i |x_i|^p`. -/
def lpPower {ι : Type*} [Fintype ι] (p : ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i : ι, |x i| ^ p

/-- Finite-coordinate `Lp` quantity, `(sum_i |x_i|^p)^(1/p)`. -/
def lp {ι : Type*} [Fintype ι] (p : ℝ) (x : ι → ℝ) : ℝ :=
  (lpPower p x) ^ (1 / p)

theorem normL1_eq_sum_abs {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    l1 x = ∑ i : ι, |x i| := rfl

theorem normL2Sq_eq_sum_sq {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    l2Sq x = ∑ i : ι, x i ^ 2 := rfl

theorem dot_eq_sum_mul {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    dot x y = ∑ i : ι, x i * y i := rfl

theorem dot_self_eq_l2Sq {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    dot x x = l2Sq x := by
  simp [dot, l2Sq, pow_two]

theorem dot_comm {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    dot x y = dot y x := by
  simp [dot, mul_comm]

/--
Hilbert-space projection estimate used to turn one strong alignment and one
small cross-alignment into a same-family correlation bound.
-/
theorem real_inner_le_abs_cross_add_sqrt_one_sub_sq_of_unit
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {u v w : F} {alpha beta : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (halpha : alpha ≤ inner ℝ u w) (halpha_nonneg : 0 ≤ alpha)
    (hcross : |inner ℝ v w| ≤ beta) :
    inner ℝ u v ≤ beta + Real.sqrt (1 - alpha ^ 2) := by
  let a : ℝ := inner ℝ u w
  let b : ℝ := inner ℝ v w
  let uperp : F := u - a • w
  let vperp : F := v - b • w
  have ha_nonneg : 0 ≤ a := le_trans halpha_nonneg halpha
  have ha_abs_le_one : |a| ≤ 1 := by
    have h := abs_real_inner_le_norm u w
    rw [hu, hw, mul_one] at h
    simpa [a] using h
  have ha_le_one : a ≤ 1 := (le_abs_self a).trans ha_abs_le_one
  have hdecomp : inner ℝ u v = a * b + inner ℝ uperp vperp := by
    dsimp [uperp, vperp, a, b]
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    simp [inner_smul_left, inner_smul_right, real_inner_comm, hw]
  have hab_le_beta : a * b ≤ beta := by
    have hab_le_abs : a * b ≤ |b| := by
      by_cases hb : 0 ≤ b
      · have hb_abs : |b| = b := abs_of_nonneg hb
        rw [hb_abs]
        nlinarith
      · have hbneg : b < 0 := lt_of_not_ge hb
        have hb_abs : |b| = -b := abs_of_neg hbneg
        rw [hb_abs]
        nlinarith
    exact hab_le_abs.trans hcross
  have huperp_sq : ‖uperp‖ ^ 2 = 1 - a ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    dsimp [uperp, a]
    rw [inner_sub_sub_self]
    simp [inner_smul_left, inner_smul_right, real_inner_comm, norm_smul, hu, hw]
    ring_nf
  have hvperp_sq : ‖vperp‖ ^ 2 = 1 - b ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    dsimp [vperp, b]
    rw [inner_sub_sub_self]
    simp [inner_smul_left, inner_smul_right, real_inner_comm, norm_smul, hv, hw]
    ring_nf
  have huperp_norm_le : ‖uperp‖ ≤ Real.sqrt (1 - alpha ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    rw [huperp_sq]
    nlinarith
  have hvperp_norm_le_one : ‖vperp‖ ≤ 1 := by
    have hs : ‖vperp‖ ^ 2 ≤ 1 := by
      rw [hvperp_sq]
      nlinarith [sq_nonneg b]
    have h := Real.le_sqrt_of_sq_le hs
    simpa using h
  have hperp_le : inner ℝ uperp vperp ≤ Real.sqrt (1 - alpha ^ 2) := by
    have h1 : inner ℝ uperp vperp ≤ |inner ℝ uperp vperp| := le_abs_self _
    have h2 := abs_real_inner_le_norm uperp vperp
    have hsqrt_nonneg : 0 ≤ Real.sqrt (1 - alpha ^ 2) := Real.sqrt_nonneg _
    have h3 : ‖uperp‖ * ‖vperp‖ ≤ Real.sqrt (1 - alpha ^ 2) * 1 := by
      exact mul_le_mul huperp_norm_le hvperp_norm_le_one (norm_nonneg _) hsqrt_nonneg
    nlinarith
  rw [hdecomp]
  nlinarith

theorem normL2_eq_sqrt_sum_sq {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    l2 x = Real.sqrt (∑ i : ι, x i ^ 2) := rfl

theorem linf_eq_sup_abs {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) :
    linf x = (Finset.univ : Finset ι).sup' Finset.univ_nonempty
      (fun i => |x i|) := rfl

theorem lpPower_eq_sum_abs_rpow {ι : Type*} [Fintype ι]
    (p : ℝ) (x : ι → ℝ) :
    lpPower p x = ∑ i : ι, |x i| ^ p := rfl

theorem lp_eq_power_sum_rpow {ι : Type*} [Fintype ι]
    (p : ℝ) (x : ι → ℝ) :
    lp p x = (∑ i : ι, |x i| ^ p) ^ (1 / p) := rfl

theorem lpPower_smul {ι : Type*} [Fintype ι]
    (p a : ℝ) (x : ι → ℝ) :
    lpPower p (fun i => a * x i) = |a| ^ p * lpPower p x := by
  rw [lpPower, lpPower, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [abs_mul, Real.mul_rpow (abs_nonneg a) (abs_nonneg (x i))]

theorem normL1_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    0 ≤ l1 x := by
  exact Finset.sum_nonneg fun i _ => abs_nonneg (x i)

theorem normL2Sq_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    0 ≤ l2Sq x := by
  exact Finset.sum_nonneg fun i _ => sq_nonneg (x i)

theorem normL2_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    0 ≤ l2 x :=
  Real.sqrt_nonneg _

theorem normL2_sq_eq_normL2Sq {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    l2 x ^ 2 = l2Sq x := by
  rw [l2]
  exact Real.sq_sqrt (normL2Sq_nonneg x)

theorem abs_dot_le_l2_mul_l2 {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) :
    |dot x y| ≤ l2 x * l2 y := by
  have hpos :
      dot x y ≤ l2 x * l2 y := by
    simpa [dot, l2, l2Sq] using
      (Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset ι) x y)
  have hneg :
      -dot x y ≤ l2 x * l2 y := by
    have h :=
      Real.sum_mul_le_sqrt_mul_sqrt
        (Finset.univ : Finset ι) (fun i => -x i) y
    simpa [dot, l2, l2Sq, Finset.sum_neg_distrib] using h
  have hleft : -(l2 x * l2 y) ≤ dot x y := by
    linarith
  exact abs_le.mpr ⟨hleft, hpos⟩

/-- Each coordinate is bounded by the finite-coordinate `L2` norm. -/
theorem normL2_coord_abs_le {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (i : ι) :
    |x i| ≤ l2 x := by
  rw [l2]
  exact Real.abs_le_sqrt <| by
    rw [l2Sq]
    exact Finset.single_le_sum
      (fun j _hj => sq_nonneg (x j))
      (Finset.mem_univ i)

theorem normL2_smul {ι : Type*} [Fintype ι]
    (a : ℝ) (x : ι → ℝ) :
    l2 (fun i => a * x i) = |a| * l2 x := by
  rw [l2, l2]
  have hsum :
      l2Sq (fun i => a * x i) = a ^ 2 * l2Sq x := by
    rw [l2Sq, l2Sq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [hsum, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

theorem linf_nonneg {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    0 ≤ linf x := by
  rw [linf]
  exact Finset.le_sup'_of_le _ Finset.univ_nonempty.choose_spec
    (abs_nonneg (x Finset.univ_nonempty.choose))

theorem lpPower_nonneg {ι : Type*} [Fintype ι] (p : ℝ) (x : ι → ℝ) :
    0 ≤ lpPower p x := by
  exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg (x i)) p

theorem lpPower_pos_of_exists_ne_zero {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 0 < p) {x : ι → ℝ} (hx : ∃ i, x i ≠ 0) :
    0 < lpPower p x := by
  rcases hx with ⟨i, hi⟩
  rw [lpPower]
  exact Finset.sum_pos'
    (fun j _ => Real.rpow_nonneg (abs_nonneg (x j)) p)
    ⟨i, Finset.mem_univ i, Real.rpow_pos_of_pos (abs_pos.mpr hi) p⟩

theorem normL1_pos_of_exists_ne_zero {ι : Type*} [Fintype ι]
    {x : ι → ℝ} (hx : ∃ i, x i ≠ 0) :
    0 < l1 x := by
  rcases hx with ⟨i, hi⟩
  rw [l1]
  exact Finset.sum_pos'
    (fun j _ => abs_nonneg (x j))
    ⟨i, Finset.mem_univ i, abs_pos.mpr hi⟩

theorem normL2Sq_pos_of_exists_ne_zero {ι : Type*} [Fintype ι]
    {x : ι → ℝ} (hx : ∃ i, x i ≠ 0) :
    0 < l2Sq x := by
  rcases hx with ⟨i, hi⟩
  rw [l2Sq]
  exact Finset.sum_pos'
    (fun j _ => sq_nonneg (x j))
    ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩

theorem normL2_pos_of_exists_ne_zero {ι : Type*} [Fintype ι]
    {x : ι → ℝ} (hx : ∃ i, x i ≠ 0) :
    0 < l2 x := by
  exact Real.sqrt_pos_of_pos (normL2Sq_pos_of_exists_ne_zero hx)

theorem linf_pos_of_exists_ne_zero {ι : Type*} [Fintype ι] [Nonempty ι]
    {x : ι → ℝ} (hx : ∃ i, x i ≠ 0) :
    0 < linf x := by
  rcases hx with ⟨i, hi⟩
  rw [linf]
  exact lt_of_lt_of_le (abs_pos.mpr hi)
    (Finset.le_sup'
      (s := (Finset.univ : Finset ι))
      (f := fun j => |x j|)
      (Finset.mem_univ i))

theorem lp_nonneg {ι : Type*} [Fintype ι] (p : ℝ) (x : ι → ℝ) :
    0 ≤ lp p x := by
  exact Real.rpow_nonneg (lpPower_nonneg p x) (1 / p)

theorem lp_smul_of_pos {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 0 < p) (a : ℝ) (x : ι → ℝ) :
    lp p (fun i => a * x i) = |a| * lp p x := by
  have hp_ne : p ≠ 0 := ne_of_gt hp
  rw [lp, lpPower_smul, Real.mul_rpow
    (Real.rpow_nonneg (abs_nonneg a) p)
    (lpPower_nonneg p x)]
  congr 1
  rw [← Real.rpow_mul (abs_nonneg a) p (1 / p)]
  have hmul : p * (1 / p) = 1 := by field_simp [hp_ne]
  rw [hmul, Real.rpow_one]

theorem lp_pos_of_exists_ne_zero {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 0 < p) {x : ι → ℝ} (hx : ∃ i, x i ≠ 0) :
    0 < lp p x := by
  rw [lp]
  exact Real.rpow_pos_of_pos (lpPower_pos_of_exists_ne_zero hp hx) (1 / p)

theorem normL1_zero {ι : Type*} [Fintype ι] :
    l1 (fun _ : ι => (0 : ℝ)) = 0 := by
  simp [l1]

theorem normL2Sq_zero {ι : Type*} [Fintype ι] :
    l2Sq (fun _ : ι => (0 : ℝ)) = 0 := by
  simp [l2Sq]

theorem normL2_zero {ι : Type*} [Fintype ι] :
    l2 (fun _ : ι => (0 : ℝ)) = 0 := by
  simp [l2, l2Sq]

theorem linf_zero {ι : Type*} [Fintype ι] [Nonempty ι] :
    linf (fun _ : ι => (0 : ℝ)) = 0 := by
  rw [linf]
  exact Finset.sup'_eq_of_forall
    (s := (Finset.univ : Finset ι))
    (H := Finset.univ_nonempty)
    (f := fun _ : ι => |(0 : ℝ)|)
    (a := 0)
    (fun _ _ => by simp)

theorem lpPower_zero_of_pos {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 0 < p) :
    lpPower p (fun _ : ι => (0 : ℝ)) = 0 := by
  simp [lpPower, Real.zero_rpow hp.ne']

theorem lp_zero_of_pos {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 0 < p) :
    lp p (fun _ : ι => (0 : ℝ)) = 0 := by
  simp [lp, lpPower_zero_of_pos (ι := ι) hp, Real.zero_rpow, hp.ne']

theorem normL1_sub_self {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    l1 (fun i => x i - x i) = 0 := by
  simpa using (normL1_zero (ι := ι))

theorem normL2Sq_sub_self {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    l2Sq (fun i => x i - x i) = 0 := by
  simpa using (normL2Sq_zero (ι := ι))

theorem normL2_sub_self {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    l2 (fun i => x i - x i) = 0 := by
  simpa using (normL2_zero (ι := ι))

theorem linf_sub_self {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    linf (fun i => x i - x i) = 0 := by
  simpa using (linf_zero (ι := ι))

theorem lpPower_sub_self_of_pos {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 0 < p) (x : ι → ℝ) :
    lpPower p (fun i => x i - x i) = 0 := by
  simpa using (lpPower_zero_of_pos (ι := ι) hp)

theorem lp_sub_self_of_pos {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 0 < p) (x : ι → ℝ) :
    lp p (fun i => x i - x i) = 0 := by
  simpa using (lp_zero_of_pos (ι := ι) hp)

/-! ## Bridges to mathlib finite-product Lp norms -/

/--
The explicit finite `L1` formula is mathlib's `PiLp 1` norm on a finite
real coordinate product.
-/
theorem normL1_eq_piLp_norm_L1 {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    l1 x =
      ‖(WithLp.toLp (1 : ENNReal) x :
        @PiLp (1 : ENNReal) ι (fun _ => ℝ))‖ := by
  rw [l1, PiLp.norm_eq_of_L1]
  simp

/--
The explicit finite `L2` formula is mathlib's `PiLp 2` norm on a finite
real coordinate product.
-/
theorem normL2_eq_piLp_norm_L2 {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    l2 x =
      ‖(WithLp.toLp (2 : ENNReal) x :
        @PiLp (2 : ENNReal) ι (fun _ => ℝ))‖ := by
  rw [l2, l2Sq, PiLp.norm_eq_of_L2]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  simp [sq_abs]

theorem piLp_inner_eq_dot {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) :
    inner ℝ
      (WithLp.toLp (2 : ENNReal) x : @PiLp (2 : ENNReal) ι (fun _ => ℝ))
      (WithLp.toLp (2 : ENNReal) y : @PiLp (2 : ENNReal) ι (fun _ => ℝ)) =
      dot x y := by
  rw [PiLp.inner_apply]
  rw [dot]
  apply Finset.sum_congr rfl
  intro i _hi
  change RCLike.re (y i * (starRingEnd ℝ) (x i)) = x i * y i
  simp [mul_comm]

/--
Finite-coordinate projection estimate, stated with the explicit `l2` and
`dot` APIs used by paper formalizations.
-/
theorem dot_le_abs_cross_add_sqrt_one_sub_sq_of_l2_unit
    {ι : Type*} [Fintype ι] {u v w : ι → ℝ} {alpha beta : ℝ}
    (hu : l2 u = 1) (hv : l2 v = 1) (hw : l2 w = 1)
    (halpha : alpha ≤ dot u w) (halpha_nonneg : 0 ≤ alpha)
    (hcross : |dot v w| ≤ beta) :
    dot u v ≤ beta + Real.sqrt (1 - alpha ^ 2) := by
  let U : @PiLp (2 : ENNReal) ι (fun _ => ℝ) := WithLp.toLp (2 : ENNReal) u
  let V : @PiLp (2 : ENNReal) ι (fun _ => ℝ) := WithLp.toLp (2 : ENNReal) v
  let W : @PiLp (2 : ENNReal) ι (fun _ => ℝ) := WithLp.toLp (2 : ENNReal) w
  have hU : ‖U‖ = 1 := by
    simpa [U] using (normL2_eq_piLp_norm_L2 u).symm.trans hu
  have hV : ‖V‖ = 1 := by
    simpa [V] using (normL2_eq_piLp_norm_L2 v).symm.trans hv
  have hW : ‖W‖ = 1 := by
    simpa [W] using (normL2_eq_piLp_norm_L2 w).symm.trans hw
  have halpha' : alpha ≤ inner ℝ U W := by
    simpa [U, W, piLp_inner_eq_dot] using halpha
  have hcross' : |inner ℝ V W| ≤ beta := by
    simpa [V, W, piLp_inner_eq_dot] using hcross
  have h :=
    real_inner_le_abs_cross_add_sqrt_one_sub_sq_of_unit
      hU hV hW halpha' halpha_nonneg hcross'
  simpa [U, V, piLp_inner_eq_dot] using h

/--
The explicit finite `L∞` formula is mathlib's `PiLp ∞` norm on a finite
real coordinate product.
-/
theorem linf_eq_piLp_norm_Linf {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    linf x =
      ‖(WithLp.toLp (⊤ : ENNReal) x :
        @PiLp (⊤ : ENNReal) ι (fun _ => ℝ))‖ := by
  rw [linf, PiLp.norm_eq_ciSup]
  simpa using (Finset.sup'_univ_eq_ciSup (fun i : ι => |x i|))

/--
For a positive finite exponent represented in `ENNReal`, mathlib's `PiLp`
norm is the same explicit finite power-sum formula.
-/
theorem piLp_norm_eq_lp_of_ENNReal
    {ι : Type*} [Fintype ι] (p : ENNReal) (hp : 0 < p.toReal)
    (x : ι → ℝ) :
    ‖(WithLp.toLp p x : @PiLp p ι (fun _ => ℝ))‖ =
      (∑ i : ι, ‖x i‖ ^ p.toReal) ^ (1 / p.toReal) := by
  simpa using
    (PiLp.norm_eq_sum (β := fun _ : ι => ℝ) hp
      (WithLp.toLp p x : @PiLp p ι (fun _ => ℝ)))

/--
For a positive finite exponent represented in `ENNReal`, the explicit
finite `Lp` formula at `p.toReal` equals mathlib's `PiLp p` norm.
-/
theorem lp_toReal_eq_piLp_norm
    {ι : Type*} [Fintype ι] (p : ENNReal) (hp : 0 < p.toReal)
    (x : ι → ℝ) :
    lp p.toReal x =
      ‖(WithLp.toLp p x : @PiLp p ι (fun _ => ℝ))‖ := by
  rw [lp, lpPower, piLp_norm_eq_lp_of_ENNReal p hp]
  apply congrArg (fun s => s ^ (1 / p.toReal))
  apply Finset.sum_congr rfl
  intro i _hi
  simp

end

end FiniteDimensionalNorms
end EconCSLib
