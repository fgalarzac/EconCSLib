import EconCSLib.Foundations.Probability.Conditional

open scoped BigOperators

namespace EconCSLib

/-!
# Independent Products of Finite PMFs

Small reusable constructors for independent products of two finite PMFs with
possibly different sample spaces.
-/

/-- Independent product PMF on `α × β`. -/
noncomputable def pmfProd {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (ν : PMF β) : PMF (α × β) :=
  PMF.ofFintype (fun p : α × β => μ p.1 * ν p.2) (by
    classical
    have hμ : ∑ a : α, μ a = 1 := by
      rw [← PMF.tsum_coe μ, tsum_fintype]
    have hν : ∑ b : β, ν b = 1 := by
      rw [← PMF.tsum_coe ν, tsum_fintype]
    calc
      ∑ p : α × β, μ p.1 * ν p.2
          = ∑ a : α, ∑ b : β, μ a * ν b := by
            rw [Fintype.sum_prod_type]
      _ = ∑ a : α, μ a * (∑ b : β, ν b) := by
            simp [Finset.mul_sum]
      _ = 1 := by
            simp [hμ, hν])

/--
Independent product PMF over a finite dependent family of coordinate spaces.
At coordinate `i`, the draw has law `μ i`.
-/
noncomputable def pmfPi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i : ι, Fintype (α i)]
    (μ : ∀ i : ι, PMF (α i)) : PMF ((i : ι) → α i) :=
  PMF.ofFintype (fun f : (i : ι) → α i => ∏ i : ι, μ i (f i)) (by
    classical
    have hcoord : ∀ i : ι, ∑ a : α i, μ i a = 1 := by
      intro i
      rw [← PMF.tsum_coe (μ i), tsum_fintype]
    calc
      ∑ f : ((i : ι) → α i), ∏ i : ι, μ i (f i)
          = ∑ f ∈ Fintype.piFinset
              (fun i : ι => (Finset.univ : Finset (α i))),
              ∏ i : ι, μ i (f i) := by
            simp
      _ = ∏ i : ι, ∑ a ∈ (Finset.univ : Finset (α i)), μ i a := by
            symm
            exact Finset.prod_univ_sum
              (t := fun i : ι => (Finset.univ : Finset (α i)))
              (f := fun i a => μ i a)
      _ = 1 := by simp [hcoord])

@[simp]
theorem pmfProd_apply {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (ν : PMF β) (p : α × β) :
    pmfProd μ ν p = μ p.1 * ν p.2 := by
  simp [pmfProd]

@[simp]
theorem pmfPi_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i : ι, Fintype (α i)]
    (μ : ∀ i : ι, PMF (α i)) (f : (i : ι) → α i) :
    pmfPi μ f = ∏ i : ι, μ i (f i) := by
  simp [pmfPi]

@[simp]
theorem pmfProd_apply_toReal {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (ν : PMF β) (p : α × β) :
    (pmfProd μ ν p).toReal = (μ p.1).toReal * (ν p.2).toReal := by
  rw [pmfProd_apply]
  exact ENNReal.toReal_mul

@[simp]
theorem pmfPi_apply_toReal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i : ι, Fintype (α i)]
    (μ : ∀ i : ι, PMF (α i)) (f : (i : ι) → α i) :
    (pmfPi μ f).toReal = ∏ i : ι, (μ i (f i)).toReal := by
  rw [pmfPi_apply]
  simp

/--
Split a same-codomain finite function into two distinguished coordinates and
the remaining coordinates.
-/
def twoCoordFunEquivProdRest {ι α : Type*} [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) :
    (ι → α) ≃ (α × α) × ({k : ι // k ≠ i ∧ k ≠ j} → α) where
  toFun f := ((f i, f j), fun k => f k.1)
  invFun x k :=
    if hi : k = i then x.1.1
    else if hj : k = j then x.1.2
    else x.2 ⟨k, hi, hj⟩
  left_inv f := by
    funext k
    by_cases hi : k = i
    · subst hi
      simp
    · by_cases hj : k = j
      · subst hj
        simp [hi]
      · simp [hi, hj]
  right_inv x := by
    apply Prod.ext
    · apply Prod.ext
      · simp
      · simp [Ne.symm hij]
    · funext k
      simp [k.2.1, k.2.2]

/--
Under a finite independent product with same-codomain coordinate laws, the
two-coordinate marginal expectation is the pair-product expectation.
-/
theorem pmfExp_pmfPi_twoCoord_eq_pairExp
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α]
    (μ : ι → PMF α) {i j : ι} (hij : i ≠ j)
    (F : α → α → ℝ) :
    pmfExp (pmfPi (fun k : ι => μ k)) (fun f : ι → α => F (f i) (f j)) =
      pmfPairExp (μ i) (μ j) F := by
  classical
  let Rest := {k : ι // k ≠ i ∧ k ≠ j}
  let e := twoCoordFunEquivProdRest (α := α) i j hij
  have hrest_mass :
      ∑ rest : Rest → α, ∏ k : Rest, (μ k.1 (rest k)).toReal = 1 := by
    have hcoord : ∀ k : Rest, ∑ a : α, (μ k.1 a).toReal = 1 := by
      intro k
      exact pmfToRealSum (μ k.1)
    calc
      ∑ rest : Rest → α, ∏ k : Rest, (μ k.1 (rest k)).toReal
          = ∏ k : Rest, ∑ a : α, (μ k.1 a).toReal := by
            symm
            simpa using
              (Finset.prod_univ_sum
                (t := fun _k : Rest => (Finset.univ : Finset α))
                (f := fun k a => (μ k.1 a).toReal))
      _ = 1 := by simp [hcoord]
  have hprod_split :
      ∀ x : (α × α) × (Rest → α),
        (∏ k : ι, (μ k ((e.symm x) k)).toReal) =
          (μ i x.1.1).toReal * (μ j x.1.2).toReal *
            ∏ k : Rest, (μ k.1 (x.2 k)).toReal := by
    intro x
    let g : ι → ℝ := fun k => (μ k ((e.symm x) k)).toReal
    have hi_eval : g i = (μ i x.1.1).toReal := by
      simp [g, e, twoCoordFunEquivProdRest]
    have hj_eval : g j = (μ j x.1.2).toReal := by
      simp [g, e, twoCoordFunEquivProdRest, Ne.symm hij]
    have hrest :
        (∏ k ∈ ({i}ᶜ : Finset ι) \ {j}, g k) =
          ∏ k : Rest, (μ k.1 (x.2 k)).toReal := by
      rw [Finset.prod_subtype
        (s := ({i}ᶜ : Finset ι) \ {j})
        (p := fun k : ι => k ≠ i ∧ k ≠ j)]
      · refine Finset.prod_congr rfl ?_
        intro k _
        simp [g, e, twoCoordFunEquivProdRest, k.2.1, k.2.2]
      · intro k
        simp
    calc
      ∏ k : ι, (μ k ((e.symm x) k)).toReal
          = ∏ k : ι, g k := rfl
      _ = g i * ∏ k ∈ ({i}ᶜ : Finset ι), g k := by
            rw [Fintype.prod_eq_mul_prod_compl]
      _ = g i * (g j * ∏ k ∈ ({i}ᶜ : Finset ι) \ {j}, g k) := by
            congr 1
            rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem]
            simp [hij.symm]
      _ = (μ i x.1.1).toReal * (μ j x.1.2).toReal *
            ∏ k : Rest, (μ k.1 (x.2 k)).toReal := by
            rw [hi_eval, hj_eval, hrest]
            ring
  unfold pmfPairExp pmfExp
  calc
    ∑ f : ι → α,
        (pmfPi (fun k : ι => μ k) f).toReal * F (f i) (f j)
        =
        ∑ x : (α × α) × (Rest → α),
          (pmfPi (fun k : ι => μ k) (e.symm x)).toReal *
            F ((e.symm x) i) ((e.symm x) j) := by
          simpa [e] using
            (Equiv.sum_comp e.symm
              (fun f : ι → α =>
                (pmfPi (fun k : ι => μ k) f).toReal * F (f i) (f j))).symm
    _ =
        ∑ x : (α × α) × (Rest → α),
          ((μ i x.1.1).toReal * (μ j x.1.2).toReal *
              ∏ k : Rest, (μ k.1 (x.2 k)).toReal) *
            F x.1.1 x.1.2 := by
          refine Finset.sum_congr rfl ?_
          intro x _
          rw [pmfPi_apply_toReal, hprod_split x]
          simp [e, twoCoordFunEquivProdRest, Ne.symm hij]
    _ =
        ∑ pair : α × α, ∑ rest : Rest → α,
          ((μ i pair.1).toReal * (μ j pair.2).toReal *
              ∏ k : Rest, (μ k.1 (rest k)).toReal) *
            F pair.1 pair.2 := by
          simpa [Finset.univ_product_univ] using
            (Finset.sum_product'
              (s := (Finset.univ : Finset (α × α)))
              (t := (Finset.univ : Finset (Rest → α)))
              (f := fun pair rest =>
                ((μ i pair.1).toReal * (μ j pair.2).toReal *
                    ∏ k : Rest, (μ k.1 (rest k)).toReal) *
                  F pair.1 pair.2))
    _ =
        ∑ pair : α × α,
          ((μ i pair.1).toReal * (μ j pair.2).toReal) *
            F pair.1 pair.2 := by
          refine Finset.sum_congr rfl ?_
          intro pair _
          calc
            ∑ rest : Rest → α,
              ((μ i pair.1).toReal * (μ j pair.2).toReal *
                  ∏ k : Rest, (μ k.1 (rest k)).toReal) *
                F pair.1 pair.2
                =
                ((μ i pair.1).toReal * (μ j pair.2).toReal *
                    F pair.1 pair.2) *
                  ∑ rest : Rest → α,
                    ∏ k : Rest, (μ k.1 (rest k)).toReal := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl ?_
                  intro rest _
                  ring
            _ = ((μ i pair.1).toReal * (μ j pair.2).toReal) *
                  F pair.1 pair.2 := by
                  rw [hrest_mass]
                  ring
    _ =
        ∑ a : α, (μ i a).toReal *
          ∑ b : α, (μ j b).toReal * F a b := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro b _
          ring

/-- Expectations under `pmfProd` are independent pair expectations. -/
theorem pmfExp_pmfProd_eq_pairExp {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (f : α × β → ℝ) :
    pmfExp (pmfProd μ ν) f =
      pmfPairExp μ ν (fun a b => f (a, b)) := by
  classical
  simp [pmfExp, pmfPairExp]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro b _
  ring

/--
Finite law of total variance for two independent PMF draws.  The first term is
the expected conditional variance in the second coordinate and the second is
the variance of the conditional expectation in the first coordinate.
-/
theorem pmfVariance_pmfProd_eq_exp_condVariance_add_variance_condExp
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (F : α → β → ℝ) :
    pmfVariance (pmfProd μ ν) (fun x : α × β => F x.1 x.2) =
      pmfExp μ (fun a => pmfVariance ν (fun b => F a b)) +
        pmfVariance μ (fun a => pmfExp ν (fun b => F a b)) := by
  have hcond_var :
      pmfExp μ (fun a => pmfVariance ν (fun b => F a b)) =
        pmfPairExp μ ν (fun a b => F a b ^ 2) -
          pmfExp μ (fun a => (pmfExp ν (fun b => F a b)) ^ 2) := by
    calc
      pmfExp μ (fun a => pmfVariance ν (fun b => F a b)) =
          pmfExp μ
            (fun a =>
              pmfExp ν (fun b => F a b ^ 2) -
                (pmfExp ν (fun b => F a b)) ^ 2) := by
              refine pmfExp_congr μ ?_
              intro a
              exact pmfVariance_eq_exp_sq_sub_sq_exp ν (fun b => F a b)
      _ =
          pmfExp μ (fun a => pmfExp ν (fun b => F a b ^ 2)) -
            pmfExp μ (fun a => (pmfExp ν (fun b => F a b)) ^ 2) := by
              rw [pmfExp_sub]
      _ =
          pmfPairExp μ ν (fun a b => F a b ^ 2) -
            pmfExp μ (fun a => (pmfExp ν (fun b => F a b)) ^ 2) := by
              rfl
  have hcond_exp_var :
      pmfVariance μ (fun a => pmfExp ν (fun b => F a b)) =
        pmfExp μ (fun a => (pmfExp ν (fun b => F a b)) ^ 2) -
          (pmfPairExp μ ν F) ^ 2 := by
    rw [pmfVariance_eq_exp_sq_sub_sq_exp]
    rfl
  have hsecond :
      pmfExp (pmfProd μ ν) (fun x : α × β => F x.1 x.2 ^ 2) =
        pmfPairExp μ ν (fun a b => F a b ^ 2) :=
    pmfExp_pmfProd_eq_pairExp μ ν (fun x : α × β => F x.1 x.2 ^ 2)
  have hmean :
      pmfExp (pmfProd μ ν) (fun x : α × β => F x.1 x.2) =
        pmfPairExp μ ν F :=
    pmfExp_pmfProd_eq_pairExp μ ν (fun x : α × β => F x.1 x.2)
  rw [pmfVariance_eq_exp_sq_sub_sq_exp, hsecond, hmean]
  rw [hcond_var, hcond_exp_var]
  ring

/--
The expected conditional variance in a product draw is half the expected
squared change after resampling the second coordinate independently.
-/
theorem pmfExp_condVariance_eq_half_pmfPairExp_resample_right
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (F : α → β → ℝ) :
    pmfExp μ (fun a => pmfVariance ν (fun b => F a b)) =
      (1 / 2 : ℝ) *
        pmfPairExp μ ν
          (fun a b => pmfExp ν (fun b' => (F a b - F a b') ^ 2)) := by
  calc
    pmfExp μ (fun a => pmfVariance ν (fun b => F a b)) =
        pmfExp μ
          (fun a =>
            (1 / 2 : ℝ) *
              pmfPairExp ν ν (fun b b' => (F a b - F a b') ^ 2)) := by
          refine pmfExp_congr μ ?_
          intro a
          exact pmfVariance_eq_half_pmfPairExp_sq_sub ν (fun b => F a b)
    _ =
        (1 / 2 : ℝ) *
          pmfExp μ
            (fun a => pmfPairExp ν ν (fun b b' => (F a b - F a b') ^ 2)) := by
          rw [pmfExp_const_mul]
    _ =
        (1 / 2 : ℝ) *
          pmfPairExp μ ν
            (fun a b => pmfExp ν (fun b' => (F a b - F a b') ^ 2)) := by
          rfl

/--
Product variance splits into a second-coordinate resampling term and the
variance of the first-coordinate conditional expectation.
-/
theorem pmfVariance_pmfProd_eq_half_resample_right_add_variance_condExp
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (F : α → β → ℝ) :
    pmfVariance (pmfProd μ ν) (fun x : α × β => F x.1 x.2) =
      (1 / 2 : ℝ) *
        pmfPairExp μ ν
          (fun a b => pmfExp ν (fun b' => (F a b - F a b') ^ 2)) +
        pmfVariance μ (fun a => pmfExp ν (fun b => F a b)) := by
  rw [pmfVariance_pmfProd_eq_exp_condVariance_add_variance_condExp]
  rw [pmfExp_condVariance_eq_half_pmfPairExp_resample_right]

/--
Taking an independent conditional expectation cannot increase the independent
copy variance: this is the finite Jensen step in Efron--Stein tensorization.
-/
theorem pmfVariance_condExp_le_half_pmfPairExp_resample_left
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (F : α → β → ℝ) :
    pmfVariance μ (fun a => pmfExp ν (fun b => F a b)) ≤
      (1 / 2 : ℝ) *
        pmfPairExp μ μ
          (fun a a' => pmfExp ν (fun b => (F a b - F a' b) ^ 2)) := by
  rw [pmfVariance_eq_half_pmfPairExp_sq_sub]
  apply mul_le_mul_of_nonneg_left
  · unfold pmfPairExp
    refine pmfExp_le_pmfExp_of_forall_le μ _ _ ?_
    intro a
    refine pmfExp_le_pmfExp_of_forall_le μ _ _ ?_
    intro a'
    have h := pmfExp_sq_le_pmfExp_sq ν (fun b => F a b - F a' b)
    rw [pmfExp_sub] at h
    exact h
  · norm_num

/--
Two-coordinate finite Efron--Stein inequality, obtained by resampling either
independent coordinate.  Iterating this is the variance route for iid lists.
-/
theorem pmfVariance_pmfProd_le_half_sum_resample_coordinates
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (F : α → β → ℝ) :
    pmfVariance (pmfProd μ ν) (fun x : α × β => F x.1 x.2) ≤
      (1 / 2 : ℝ) *
          pmfPairExp μ ν
            (fun a b => pmfExp ν (fun b' => (F a b - F a b') ^ 2)) +
        (1 / 2 : ℝ) *
          pmfPairExp μ μ
            (fun a a' => pmfExp ν (fun b => (F a b - F a' b) ^ 2)) := by
  rw [pmfVariance_pmfProd_eq_half_resample_right_add_variance_condExp]
  gcongr
  exact pmfVariance_condExp_le_half_pmfPairExp_resample_left μ ν F

/-- Expected squared change after independently resampling coordinate `i`. -/
noncomputable def pmfResampleEnergy
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (μ : PMF α) (F : (ι → α) → ℝ) (i : ι) : ℝ :=
  pmfPairExp (pmfProduct ι α μ) μ
    (fun sample replacement =>
      (F sample - F (Function.update sample i replacement)) ^ 2)

/-- Resampling the distinguished `none` coordinate of an `Option` product. -/
theorem pmfResampleEnergy_option_none
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (μ : PMF α) (F : (Option ι → α) → ℝ) :
    pmfResampleEnergy μ F none =
      pmfPairExp (pmfProduct ι α μ) μ
        (fun sample newItem =>
          pmfExp μ
            (fun replacement =>
              (F (extendDraw sample newItem) -
                F (extendDraw sample replacement)) ^ 2)) := by
  classical
  unfold pmfResampleEnergy pmfPairExp
  rw [pmfExp_pmfProduct_option_eq_pairExp]
  refine pmfExp_congr (pmfProduct ι α μ) ?_
  intro sample
  refine pmfExp_congr μ ?_
  intro newItem
  refine pmfExp_congr μ ?_
  intro replacement
  have hupdate :
      Function.update (extendDraw sample newItem) none replacement =
        extendDraw sample replacement := by
    funext index
    cases index <;> simp [extendDraw]
  dsimp
  rw [hupdate]

/-- Resampling an inherited `some i` coordinate of an `Option` product. -/
theorem pmfResampleEnergy_option_some
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (μ : PMF α) (F : (Option ι → α) → ℝ) (i : ι) :
    pmfResampleEnergy μ F (some i) =
      pmfPairExp (pmfProduct ι α μ) μ
        (fun sample newItem =>
          pmfExp μ
            (fun replacement =>
              (F (extendDraw sample newItem) -
                F (extendDraw (Function.update sample i replacement) newItem)) ^ 2)) := by
  classical
  unfold pmfResampleEnergy pmfPairExp
  rw [pmfExp_pmfProduct_option_eq_pairExp]
  refine pmfExp_congr (pmfProduct ι α μ) ?_
  intro sample
  refine pmfExp_congr μ ?_
  intro newItem
  refine pmfExp_congr μ ?_
  intro replacement
  have hupdate :
      Function.update (extendDraw sample newItem) (some i) replacement =
        extendDraw (Function.update sample i replacement) newItem := by
    funext index
    cases index with
    | none => simp [extendDraw]
    | some j =>
        by_cases hji : j = i
        · subst hji
          simp [extendDraw]
        · simp [Function.update_of_ne, extendDraw, hji]
  dsimp
  rw [hupdate]

/-- The two iid replacement draws in an inherited-coordinate energy may swap. -/
theorem pmfResampleEnergy_option_some_swap
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (μ : PMF α) (F : (Option ι → α) → ℝ) (i : ι) :
    pmfResampleEnergy μ F (some i) =
      pmfPairExp (pmfProduct ι α μ) μ
        (fun sample replacement =>
          pmfExp μ
            (fun newItem =>
              (F (extendDraw sample newItem) -
                F (extendDraw (Function.update sample i replacement) newItem)) ^ 2)) := by
  rw [pmfResampleEnergy_option_some]
  unfold pmfPairExp
  refine pmfExp_congr (pmfProduct ι α μ) ?_
  intro sample
  exact pmfPairExp_swap μ μ
    (fun newItem replacement =>
      (F (extendDraw sample newItem) -
        F (extendDraw (Function.update sample i replacement) newItem)) ^ 2)

/-- Resampling the distinguished coordinate of an iid `Option` product preserves its law. -/
theorem pmfPairExp_pmfProduct_option_update_none_eq_pmfExp
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (μ : PMF α) (F : (Option ι → α) → ℝ) :
    pmfPairExp (pmfProduct (Option ι) α μ) μ
        (fun sample replacement => F (Function.update sample none replacement)) =
      pmfExp (pmfProduct (Option ι) α μ) F := by
  classical
  unfold pmfPairExp
  rw [pmfExp_pmfProduct_option_eq_pairExp]
  calc
    pmfPairExp (pmfProduct ι α μ) μ
        (fun sample newItem =>
          pmfExp μ
            (fun replacement =>
              F (Function.update (extendDraw sample newItem) none replacement))) =
        pmfPairExp (pmfProduct ι α μ) μ
          (fun sample _newItem => pmfExp μ (fun replacement => F (extendDraw sample replacement))) := by
          unfold pmfPairExp
          refine pmfExp_congr (pmfProduct ι α μ) ?_
          intro sample
          refine pmfExp_congr μ ?_
          intro newItem
          refine pmfExp_congr μ ?_
          intro replacement
          have hupdate :
              Function.update (extendDraw sample newItem) none replacement =
                extendDraw sample replacement := by
            funext index
            cases index <;> simp [extendDraw]
          rw [hupdate]
    _ = pmfExp (pmfProduct ι α μ)
          (fun sample => pmfExp μ (fun replacement => F (extendDraw sample replacement))) := by
          exact pmfPairExp_ignore_right (pmfProduct ι α μ) μ
            (fun sample => pmfExp μ (fun replacement => F (extendDraw sample replacement)))
    _ = pmfExp (pmfProduct (Option ι) α μ) F :=
          (pmfExp_pmfProduct_option_eq_pairExp μ F).symm

/-- Independently resampling any one coordinate of a finite iid product preserves its law. -/
theorem pmfPairExp_pmfProduct_update_eq_pmfExp
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (μ : PMF α) (F : (ι → α) → ℝ) (i : ι) :
    pmfPairExp (pmfProduct ι α μ) μ
        (fun sample replacement => F (Function.update sample i replacement)) =
      pmfExp (pmfProduct ι α μ) F := by
  classical
  let Rest := {j : ι // j ≠ i}
  let e : Option Rest ≃ ι := Equiv.optionSubtypeNe i
  let G : (Option Rest → α) → ℝ :=
    fun optionSample => F (fun j : ι => optionSample (e.symm j))
  have hoption (optionSample : Option Rest → α) (replacement : α) :
      Function.update (fun j : ι => optionSample (e.symm j)) i replacement =
        (fun j : ι => Function.update optionSample none replacement (e.symm j)) := by
    funext j
    by_cases hji : j = i
    · subst hji
      have hnone : e.symm j = none := by
        apply e.injective
        rw [e.apply_symm_apply]
        change j = Equiv.optionSubtypeNe j none
        rfl
      rw [hnone, Function.update_self, Function.update_self]
    · have hsymm : e.symm j = some ⟨j, hji⟩ := by
        simpa [e, Rest] using Equiv.optionSubtypeNe_symm_of_ne hji
      rw [hsymm, Function.update_of_ne hji]
      simpa [e, Rest, hji] using congrArg optionSample hsymm
  have htransport :
      pmfPairExp (pmfProduct ι α μ) μ
          (fun sample replacement => F (Function.update sample i replacement)) =
        pmfPairExp (pmfProduct (Option Rest) α μ) μ
          (fun optionSample replacement =>
            G (Function.update optionSample none replacement)) := by
    unfold pmfPairExp
    let H : (Option Rest → α) → ℝ :=
      fun optionSample =>
        pmfExp μ
          (fun replacement => F (Function.update
            (fun j : ι => optionSample (e.symm j)) i replacement))
    calc
      pmfExp (pmfProduct ι α μ)
          (fun sample =>
            pmfExp μ (fun replacement => F (Function.update sample i replacement))) =
          pmfExp (pmfProduct ι α μ)
            (fun sample => H (fun optionIndex : Option Rest => sample (e optionIndex))) := by
            refine pmfExp_congr (pmfProduct ι α μ) ?_
            intro sample
            unfold H
            refine pmfExp_congr μ ?_
            intro replacement
            have hlift :
                (fun j : ι => sample (e (e.symm j))) = sample := by
              funext j
              rw [e.apply_symm_apply]
            rw [hlift]
      _ = pmfExp (pmfProduct (Option Rest) α μ) H :=
            pmfExp_pmfProduct_equiv e.symm μ H
      _ = pmfExp (pmfProduct (Option Rest) α μ)
            (fun optionSample =>
              pmfExp μ
                (fun replacement => G (Function.update optionSample none replacement))) := by
            refine pmfExp_congr (pmfProduct (Option Rest) α μ) ?_
            intro optionSample
            unfold H G
            refine pmfExp_congr μ ?_
            intro replacement
            exact congrArg F (hoption optionSample replacement)
  calc
    pmfPairExp (pmfProduct ι α μ) μ
        (fun sample replacement => F (Function.update sample i replacement)) =
        pmfPairExp (pmfProduct (Option Rest) α μ) μ
          (fun optionSample replacement =>
            G (Function.update optionSample none replacement)) := htransport
    _ = pmfExp (pmfProduct (Option Rest) α μ) G :=
          pmfPairExp_pmfProduct_option_update_none_eq_pmfExp μ G
    _ = pmfExp (pmfProduct ι α μ) F := by
          calc
            pmfExp (pmfProduct (Option Rest) α μ) G =
                pmfExp (pmfProduct ι α μ)
                  (fun sample => G (fun optionIndex : Option Rest => sample (e optionIndex))) :=
                    (pmfExp_pmfProduct_equiv e.symm μ G).symm
            _ = pmfExp (pmfProduct ι α μ) F := by
                  refine pmfExp_congr (pmfProduct ι α μ) ?_
                  intro sample
                  unfold G
                  congr 1
                  funext j
                  simp [e]

/-- The old and independently resampled values have twice the common expectation. -/
theorem pmfPairExp_pmfProduct_add_resample_eq_two_pmfExp
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (μ : PMF α) (F : (ι → α) → ℝ) (i : ι) :
    pmfPairExp (pmfProduct ι α μ) μ
        (fun sample replacement => F sample + F (Function.update sample i replacement)) =
      2 * pmfExp (pmfProduct ι α μ) F := by
  rw [pmfPairExp_add]
  rw [pmfPairExp_ignore_right]
  rw [pmfPairExp_pmfProduct_update_eq_pmfExp]
  ring

/-- Jensen bounds the old-coordinate resampling energy after conditional expectation. -/
theorem pmfResampleEnergy_condExp_le_option_some
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (μ : PMF α) (F : (Option ι → α) → ℝ) (i : ι) :
    pmfResampleEnergy μ
      (fun sample => pmfExp μ (fun newItem => F (extendDraw sample newItem))) i ≤
      pmfResampleEnergy μ F (some i) := by
  rw [pmfResampleEnergy_option_some_swap]
  unfold pmfResampleEnergy pmfPairExp
  refine pmfExp_le_pmfExp_of_forall_le (pmfProduct ι α μ) _ _ ?_
  intro sample
  refine pmfExp_le_pmfExp_of_forall_le μ _ _ ?_
  intro replacement
  have h :=
    pmfExp_sq_le_pmfExp_sq μ
      (fun newItem =>
        F (extendDraw sample newItem) -
          F (extendDraw (Function.update sample i replacement) newItem))
  rw [pmfExp_sub] at h
  exact h

/-- Reindexing iid product coordinates by an equivalence preserves resampling energy. -/
theorem pmfResampleEnergy_pmfProduct_equiv
    {ι κ α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype α] [DecidableEq α]
    (e : ι ≃ κ) (μ : PMF α) (F : (κ → α) → ℝ) (i : ι) :
    pmfResampleEnergy μ
        (fun sample : ι → α => F (fun j : κ => sample (e.symm j))) i =
      pmfResampleEnergy μ F (e i) := by
  classical
  let H : (κ → α) → ℝ := fun sample =>
    pmfExp μ
      (fun replacement =>
        (F sample - F (Function.update sample (e i) replacement)) ^ 2)
  have hupdate (sample : ι → α) (replacement : α) :
      (fun j : κ => Function.update sample i replacement (e.symm j)) =
        Function.update (fun j : κ => sample (e.symm j)) (e i) replacement := by
    funext j
    by_cases hji : j = e i
    · subst hji
      rw [e.symm_apply_apply]
      rw [Function.update_self, Function.update_self]
    · have hne : e.symm j ≠ i := by
        intro h
        apply hji
        exact (e.apply_symm_apply j).symm.trans (congrArg e h)
      rw [Function.update_of_ne hne, Function.update_of_ne hji]
  unfold pmfResampleEnergy pmfPairExp
  calc
    pmfExp (pmfProduct ι α μ)
        (fun sample =>
          pmfExp μ
            (fun replacement =>
              (F (fun j : κ => sample (e.symm j)) -
                F (fun j : κ => Function.update sample i replacement (e.symm j))) ^ 2)) =
        pmfExp (pmfProduct ι α μ)
          (fun sample => H (fun j : κ => sample (e.symm j))) := by
          refine pmfExp_congr (pmfProduct ι α μ) ?_
          intro sample
          unfold H
          refine pmfExp_congr μ ?_
          intro replacement
          rw [hupdate]
    _ = pmfExp (pmfProduct κ α μ) H :=
      pmfExp_pmfProduct_equiv e μ H
    _ = pmfExp (pmfProduct κ α μ)
          (fun sample =>
            pmfExp μ
              (fun replacement =>
                (F sample - F (Function.update sample (e i) replacement)) ^ 2)) := by
          rfl

/-- An iid product on `Option ι` is variance-equivalent to an old product and one new draw. -/
theorem pmfVariance_pmfProduct_option_eq_pmfVariance_pmfProd
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (μ : PMF α) (F : (Option ι → α) → ℝ) :
    pmfVariance (pmfProduct (Option ι) α μ) F =
      pmfVariance (pmfProd (pmfProduct ι α μ) μ)
        (fun pair : (ι → α) × α => F (extendDraw pair.1 pair.2)) := by
  have hsecond :
      pmfExp (pmfProduct (Option ι) α μ) (fun sample => F sample ^ 2) =
        pmfExp (pmfProd (pmfProduct ι α μ) μ)
          (fun pair : (ι → α) × α => F (extendDraw pair.1 pair.2) ^ 2) := by
    calc
      pmfExp (pmfProduct (Option ι) α μ) (fun sample => F sample ^ 2) =
          pmfPairExp (pmfProduct ι α μ) μ
            (fun sample newItem => F (extendDraw sample newItem) ^ 2) :=
              pmfExp_pmfProduct_option_eq_pairExp μ (fun sample => F sample ^ 2)
      _ = pmfExp (pmfProd (pmfProduct ι α μ) μ)
            (fun pair : (ι → α) × α => F (extendDraw pair.1 pair.2) ^ 2) := by
              symm
              exact pmfExp_pmfProd_eq_pairExp (pmfProduct ι α μ) μ
                (fun pair : (ι → α) × α => F (extendDraw pair.1 pair.2) ^ 2)
  have hmean :
      pmfExp (pmfProduct (Option ι) α μ) F =
        pmfExp (pmfProd (pmfProduct ι α μ) μ)
          (fun pair : (ι → α) × α => F (extendDraw pair.1 pair.2)) := by
    calc
      pmfExp (pmfProduct (Option ι) α μ) F =
          pmfPairExp (pmfProduct ι α μ) μ
            (fun sample newItem => F (extendDraw sample newItem)) :=
              pmfExp_pmfProduct_option_eq_pairExp μ F
      _ = pmfExp (pmfProd (pmfProduct ι α μ) μ)
            (fun pair : (ι → α) × α => F (extendDraw pair.1 pair.2)) := by
              symm
              exact pmfExp_pmfProd_eq_pairExp (pmfProduct ι α μ) μ
                (fun pair : (ι → α) × α => F (extendDraw pair.1 pair.2))
  rw [pmfVariance_eq_exp_sq_sub_sq_exp, pmfVariance_eq_exp_sq_sub_sq_exp,
    hsecond, hmean]

/-- One Efron--Stein decomposition step for an iid product over `Option ι`. -/
theorem pmfVariance_pmfProduct_option_eq_half_resample_none_add_condExp
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (μ : PMF α) (F : (Option ι → α) → ℝ) :
    pmfVariance (pmfProduct (Option ι) α μ) F =
      (1 / 2 : ℝ) * pmfResampleEnergy μ F none +
        pmfVariance (pmfProduct ι α μ)
          (fun sample => pmfExp μ (fun newItem => F (extendDraw sample newItem))) := by
  rw [pmfVariance_pmfProduct_option_eq_pmfVariance_pmfProd]
  calc
    pmfVariance (pmfProd (pmfProduct ι α μ) μ)
        (fun pair : (ι → α) × α => F (extendDraw pair.1 pair.2)) =
        (1 / 2 : ℝ) *
          pmfPairExp (pmfProduct ι α μ) μ
            (fun sample newItem =>
              pmfExp μ
                (fun replacement =>
                  (F (extendDraw sample newItem) -
                    F (extendDraw sample replacement)) ^ 2)) +
          pmfVariance (pmfProduct ι α μ)
            (fun sample => pmfExp μ (fun newItem => F (extendDraw sample newItem))) := by
          simpa using
            (pmfVariance_pmfProd_eq_half_resample_right_add_variance_condExp
              (pmfProduct ι α μ) μ
              (fun sample newItem => F (extendDraw sample newItem)))
    _ =
        (1 / 2 : ℝ) * pmfResampleEnergy μ F none +
          pmfVariance (pmfProduct ι α μ)
            (fun sample => pmfExp μ (fun newItem => F (extendDraw sample newItem))) := by
          rw [pmfResampleEnergy_option_none]

/-- One induction step for the finite iid Efron--Stein inequality. -/
theorem pmfVariance_pmfProduct_le_half_sum_resample_option
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (μ : PMF α) (F : (Option ι → α) → ℝ)
    (hind :
      pmfVariance (pmfProduct ι α μ)
        (fun sample => pmfExp μ (fun newItem => F (extendDraw sample newItem))) ≤
        (1 / 2 : ℝ) *
          ∑ i : ι,
            pmfResampleEnergy μ
              (fun sample => pmfExp μ (fun newItem => F (extendDraw sample newItem))) i) :
    pmfVariance (pmfProduct (Option ι) α μ) F ≤
      (1 / 2 : ℝ) * ∑ i : Option ι, pmfResampleEnergy μ F i := by
  let H : (ι → α) → ℝ :=
    fun sample => pmfExp μ (fun newItem => F (extendDraw sample newItem))
  have hsum :
      (∑ i : ι, pmfResampleEnergy μ H i) ≤
        ∑ i : ι, pmfResampleEnergy μ F (some i) := by
    refine Finset.sum_le_sum ?_
    intro i _
    exact pmfResampleEnergy_condExp_le_option_some μ F i
  calc
    pmfVariance (pmfProduct (Option ι) α μ) F =
        (1 / 2 : ℝ) * pmfResampleEnergy μ F none +
          pmfVariance (pmfProduct ι α μ) H := by
          exact pmfVariance_pmfProduct_option_eq_half_resample_none_add_condExp μ F
    _ ≤ (1 / 2 : ℝ) * pmfResampleEnergy μ F none +
          (1 / 2 : ℝ) * ∑ i : ι, pmfResampleEnergy μ H i := by
          gcongr
    _ ≤ (1 / 2 : ℝ) * pmfResampleEnergy μ F none +
          (1 / 2 : ℝ) * ∑ i : ι, pmfResampleEnergy μ F (some i) := by
          gcongr
    _ = (1 / 2 : ℝ) * ∑ i : Option ι, pmfResampleEnergy μ F i := by
          rw [univ_option, Finset.sum_insertNone]
          ring

/-- Reindexing an entire finite iid resampling-energy sum by an equivalence. -/
theorem pmfResampleEnergy_sum_pmfProduct_equiv
    {ι κ α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype α] [DecidableEq α]
    (e : ι ≃ κ) (μ : PMF α) (F : (κ → α) → ℝ) :
    (∑ i : ι,
      pmfResampleEnergy μ
        (fun sample : ι → α => F (fun j : κ => sample (e.symm j))) i) =
      ∑ j : κ, pmfResampleEnergy μ F j := by
  calc
    (∑ i : ι,
        pmfResampleEnergy μ
          (fun sample : ι → α => F (fun j : κ => sample (e.symm j))) i) =
        ∑ j : κ,
          pmfResampleEnergy μ
            (fun sample : ι → α => F (fun j : κ => sample (e.symm j)))
            (e.symm j) := by
          simpa using
            (Equiv.sum_comp e.symm
              (fun i : ι =>
                pmfResampleEnergy μ
                  (fun sample : ι → α => F (fun j : κ => sample (e.symm j))) i)).symm
    _ = ∑ j : κ, pmfResampleEnergy μ F j := by
          refine Finset.sum_congr rfl ?_
          intro j _
          simpa using
            (pmfResampleEnergy_pmfProduct_equiv e μ F (e.symm j))

/-- An iid product with no coordinates has zero variance. -/
theorem pmfVariance_pmfProduct_pempty_eq_zero
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (F : (PEmpty → α) → ℝ) :
    pmfVariance (pmfProduct PEmpty α μ) F = 0 := by
  let defaultSample : PEmpty → α := fun x => PEmpty.elim x
  have hvalue : ∀ sample : PEmpty → α, F sample = F defaultSample := by
    intro sample
    congr 1
    funext x
    exact PEmpty.elim x
  have hmean : pmfExp (pmfProduct PEmpty α μ) F = F defaultSample := by
    calc
      pmfExp (pmfProduct PEmpty α μ) F =
          pmfExp (pmfProduct PEmpty α μ) (fun _ => F defaultSample) :=
            pmfExp_congr (pmfProduct PEmpty α μ) hvalue
      _ = F defaultSample := pmfExp_const (pmfProduct PEmpty α μ) (F defaultSample)
  unfold pmfVariance
  calc
    pmfExp (pmfProduct PEmpty α μ)
        (fun sample => (F sample - pmfExp (pmfProduct PEmpty α μ) F) ^ 2) =
        pmfExp (pmfProduct PEmpty α μ) (fun _ => 0) := by
          refine pmfExp_congr (pmfProduct PEmpty α μ) ?_
          intro sample
          rw [hvalue sample, hmean]
          ring
    _ = 0 := by simp

/--
Finite iid Efron--Stein inequality: variance is at most half the sum of the
expected squared changes from independently resampling individual coordinates.
-/
theorem pmfVariance_pmfProduct_le_half_sum_resample
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (μ : PMF α) (F : (ι → α) → ℝ) :
    pmfVariance (pmfProduct ι α μ) F ≤
      (1 / 2 : ℝ) * ∑ i : ι, pmfResampleEnergy μ F i := by
  classical
  let P : ∀ (κ : Type u_1) [Fintype κ], Prop :=
    fun κ _ =>
      ∀ [inst : DecidableEq κ] (G : (κ → α) → ℝ),
        pmfVariance (pmfProduct κ α μ) G ≤
          (1 / 2 : ℝ) * ∑ i : κ, pmfResampleEnergy μ G i
  have hP : P ι := by
    refine Fintype.induction_empty_option (P := P) ?_ ?_ ?_ ι
    · intro κ tau instTau e hind instDec G
      letI : Fintype κ := Fintype.ofEquiv tau e.symm
      calc
        pmfVariance (pmfProduct tau α μ) G =
            pmfVariance (pmfProduct κ α μ)
              (fun sample : κ → α => G (fun j : tau => sample (e.symm j))) := by
              exact (pmfVariance_pmfProduct_equiv e μ G).symm
        _ ≤ (1 / 2 : ℝ) *
              ∑ i : κ,
                pmfResampleEnergy μ
                  (fun sample : κ → α => G (fun j : tau => sample (e.symm j))) i :=
              hind _
        _ = (1 / 2 : ℝ) * ∑ j : tau, pmfResampleEnergy μ G j := by
              rw [pmfResampleEnergy_sum_pmfProduct_equiv e μ G]
    · intro instDec G
      have hzero : pmfVariance (pmfProduct PEmpty α μ) G = 0 := by
        let defaultSample : PEmpty → α := fun x => PEmpty.elim x
        have hvalue : ∀ sample : PEmpty → α, G sample = G defaultSample := by
          intro sample
          congr 1
          funext x
          exact PEmpty.elim x
        have hmean : pmfExp (pmfProduct PEmpty α μ) G = G defaultSample := by
          calc
            pmfExp (pmfProduct PEmpty α μ) G =
                pmfExp (pmfProduct PEmpty α μ) (fun _ => G defaultSample) :=
                  pmfExp_congr (pmfProduct PEmpty α μ) hvalue
            _ = G defaultSample := pmfExp_const (pmfProduct PEmpty α μ) (G defaultSample)
        unfold pmfVariance
        calc
          pmfExp (pmfProduct PEmpty α μ)
              (fun sample => (G sample - pmfExp (pmfProduct PEmpty α μ) G) ^ 2) =
              pmfExp (pmfProduct PEmpty α μ) (fun _ => 0) := by
                refine pmfExp_congr (pmfProduct PEmpty α μ) ?_
                intro sample
                rw [hvalue sample, hmean]
                ring
          _ = 0 := by simp
      rw [hzero]
      simp
    · intro κ instK hind instDec G
      letI : DecidableEq κ := Classical.decEq κ
      have hdec : instDec = (Option.instDecidableEq : DecidableEq (Option κ)) :=
        Subsingleton.elim _ _
      cases hdec
      exact pmfVariance_pmfProduct_le_half_sum_resample_option μ G (hind _)
  exact hP F

/--
The two-coordinate event marginal of a same-codomain finite independent product
is the independent pair-product event probability.
-/
theorem pmfProb_pmfPi_twoCoord_eq_pmfProd
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α]
    (μ : ι → PMF α) {i j : ι} (hij : i ≠ j)
    (p : α → α → Prop) [DecidableRel p] :
    pmfProb (pmfPi (fun k : ι => μ k))
        (fun f : ι → α => p (f i) (f j)) =
      pmfProb (pmfProd (μ i) (μ j))
        (fun x : α × α => p x.1 x.2) := by
  classical
  unfold pmfProb
  change
    pmfExp (pmfPi (fun k : ι => μ k))
        (fun f : ι → α => if p (f i) (f j) then (1 : ℝ) else 0) =
      pmfExp (pmfProd (μ i) (μ j))
        (fun x : α × α => if p x.1 x.2 then (1 : ℝ) else 0)
  rw [pmfExp_pmfPi_twoCoord_eq_pairExp
    (μ := μ) (i := i) (j := j) hij
    (F := fun a b => if p a b then (1 : ℝ) else 0)]
  rw [pmfExp_pmfProd_eq_pairExp]

/--
Split a dependent finite function into two distinguished coordinates and the
remaining dependent coordinates.
-/
def twoCoordDFunEquivProdRest {ι : Type*} [DecidableEq ι]
    {α : ι → Type*} (i j : ι) (hij : i ≠ j) :
    ((k : ι) → α k) ≃
      (α i × α j) ×
        ((k : {k : ι // k ≠ i ∧ k ≠ j}) → α k.1) where
  toFun f := ((f i, f j), fun k => f k.1)
  invFun x k :=
    if hi : k = i then by
      subst hi
      exact x.1.1
    else if hj : k = j then by
      subst hj
      exact x.1.2
    else x.2 ⟨k, hi, hj⟩
  left_inv f := by
    funext k
    by_cases hi : k = i
    · subst hi
      simp
    · by_cases hj : k = j
      · subst hj
        simp [hi]
      · simp [hi, hj]
  right_inv x := by
    apply Prod.ext
    · apply Prod.ext
      · simp
      · simp [hij.symm]
    · funext k
      simp [k.2.1, k.2.2]

/--
Under a finite independent dependent product, the two-coordinate marginal
expectation is the corresponding pair-product expectation.
-/
theorem pmfExp_pmfPi_twoCoord_eq_pairExp_dependent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ k : ι, Fintype (α k)]
    [∀ k : ι, DecidableEq (α k)]
    (μ : ∀ k : ι, PMF (α k)) {i j : ι} (hij : i ≠ j)
    (F : α i → α j → ℝ) :
    pmfExp (pmfPi μ) (fun f : (k : ι) → α k => F (f i) (f j)) =
      pmfPairExp (μ i) (μ j) F := by
  classical
  let Rest := {k : ι // k ≠ i ∧ k ≠ j}
  let e := twoCoordDFunEquivProdRest (α := α) i j hij
  have hrest_mass :
      ∑ rest : ((k : Rest) → α k.1),
          ∏ k : Rest, (μ k.1 (rest k)).toReal = 1 := by
    have hcoord : ∀ k : Rest, ∑ a : α k.1, (μ k.1 a).toReal = 1 := by
      intro k
      exact pmfToRealSum (μ k.1)
    calc
      ∑ rest : ((k : Rest) → α k.1),
          ∏ k : Rest, (μ k.1 (rest k)).toReal
          = ∏ k : Rest, ∑ a : α k.1, (μ k.1 a).toReal := by
            symm
            simpa [Rest] using
              (Finset.prod_univ_sum
                (t := fun k : Rest => (Finset.univ : Finset (α k.1)))
                (f := fun k a => (μ k.1 a).toReal))
      _ = 1 := by simp [hcoord]
  have hprod_split :
      ∀ x : (α i × α j) × ((k : Rest) → α k.1),
        (∏ k : ι, (μ k ((e.symm x) k)).toReal) =
          (μ i x.1.1).toReal * (μ j x.1.2).toReal *
            ∏ k : Rest, (μ k.1 (x.2 k)).toReal := by
    intro x
    let g : ι → ℝ := fun k => (μ k ((e.symm x) k)).toReal
    have hi_eval : g i = (μ i x.1.1).toReal := by
      simp [g, e, twoCoordDFunEquivProdRest]
    have hj_eval : g j = (μ j x.1.2).toReal := by
      simp [g, e, twoCoordDFunEquivProdRest, hij.symm]
    have hrest :
        (∏ k ∈ ({i}ᶜ : Finset ι) \ {j}, g k) =
          ∏ k : Rest, (μ k.1 (x.2 k)).toReal := by
      rw [Finset.prod_subtype
        (s := ({i}ᶜ : Finset ι) \ {j})
        (p := fun k : ι => k ≠ i ∧ k ≠ j)]
      · refine Finset.prod_congr rfl ?_
        intro k _
        simp [g, e, twoCoordDFunEquivProdRest, k.2.1, k.2.2]
      · intro k
        simp
    calc
      ∏ k : ι, (μ k ((e.symm x) k)).toReal
          = ∏ k : ι, g k := rfl
      _ = g i * ∏ k ∈ ({i}ᶜ : Finset ι), g k := by
            rw [Fintype.prod_eq_mul_prod_compl]
      _ = g i * (g j * ∏ k ∈ ({i}ᶜ : Finset ι) \ {j}, g k) := by
            congr 1
            rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem]
            simp [hij.symm]
      _ = (μ i x.1.1).toReal * (μ j x.1.2).toReal *
            ∏ k : Rest, (μ k.1 (x.2 k)).toReal := by
            rw [hi_eval, hj_eval, hrest]
            ring
  unfold pmfPairExp pmfExp
  calc
    ∑ f : ((k : ι) → α k),
        (pmfPi μ f).toReal * F (f i) (f j)
        =
        ∑ x : (α i × α j) × ((k : Rest) → α k.1),
          (pmfPi μ (e.symm x)).toReal *
            F ((e.symm x) i) ((e.symm x) j) := by
          simpa [e] using
            (Equiv.sum_comp e.symm
              (fun f : (k : ι) → α k =>
                (pmfPi μ f).toReal * F (f i) (f j))).symm
    _ =
        ∑ x : (α i × α j) × ((k : Rest) → α k.1),
          ((μ i x.1.1).toReal * (μ j x.1.2).toReal *
              ∏ k : Rest, (μ k.1 (x.2 k)).toReal) *
            F x.1.1 x.1.2 := by
          refine Finset.sum_congr rfl ?_
          intro x _
          rw [pmfPi_apply_toReal, hprod_split x]
          simp [e, twoCoordDFunEquivProdRest, hij.symm]
    _ =
        ∑ pair : α i × α j, ∑ rest : ((k : Rest) → α k.1),
          ((μ i pair.1).toReal * (μ j pair.2).toReal *
              ∏ k : Rest, (μ k.1 (rest k)).toReal) *
            F pair.1 pair.2 := by
          simpa [Finset.univ_product_univ] using
            (Finset.sum_product'
              (s := (Finset.univ : Finset (α i × α j)))
              (t := (Finset.univ : Finset ((k : Rest) → α k.1)))
              (f := fun pair rest =>
                ((μ i pair.1).toReal * (μ j pair.2).toReal *
                    ∏ k : Rest, (μ k.1 (rest k)).toReal) *
                  F pair.1 pair.2))
    _ =
        ∑ pair : α i × α j,
          ((μ i pair.1).toReal * (μ j pair.2).toReal) *
            F pair.1 pair.2 := by
          refine Finset.sum_congr rfl ?_
          intro pair _
          calc
            ∑ rest : ((k : Rest) → α k.1),
              ((μ i pair.1).toReal * (μ j pair.2).toReal *
                  ∏ k : Rest, (μ k.1 (rest k)).toReal) *
                F pair.1 pair.2
                =
                ((μ i pair.1).toReal * (μ j pair.2).toReal *
                    F pair.1 pair.2) *
                  ∑ rest : ((k : Rest) → α k.1),
                    ∏ k : Rest, (μ k.1 (rest k)).toReal := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl ?_
                  intro rest _
                  ring
            _ = ((μ i pair.1).toReal * (μ j pair.2).toReal) *
                  F pair.1 pair.2 := by
                  rw [hrest_mass]
                  ring
    _ =
        ∑ a : α i, (μ i a).toReal *
          ∑ b : α j, (μ j b).toReal * F a b := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro b _
          ring

/--
The two-coordinate event marginal of a finite independent dependent product is
the independent pair-product event probability.
-/
theorem pmfProb_pmfPi_twoCoord_eq_pmfProd_dependent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ k : ι, Fintype (α k)]
    [∀ k : ι, DecidableEq (α k)]
    (μ : ∀ k : ι, PMF (α k)) {i j : ι} (hij : i ≠ j)
    (p : α i → α j → Prop) [DecidableRel p] :
    pmfProb (pmfPi μ)
        (fun f : (k : ι) → α k => p (f i) (f j)) =
      pmfProb (pmfProd (μ i) (μ j))
        (fun x : α i × α j => p x.1 x.2) := by
  classical
  unfold pmfProb
  change
    pmfExp (pmfPi μ)
        (fun f : (k : ι) → α k => if p (f i) (f j) then (1 : ℝ) else 0) =
      pmfExp (pmfProd (μ i) (μ j))
        (fun x : α i × α j => if p x.1 x.2 then (1 : ℝ) else 0)
  rw [pmfExp_pmfPi_twoCoord_eq_pairExp_dependent
    (μ := μ) (i := i) (j := j) hij
    (F := fun a b => if p a b then (1 : ℝ) else 0)]
  rw [pmfExp_pmfProd_eq_pairExp]

/--
For independent finite PMFs, the probability of a product event factors.
-/
theorem pmfProb_pmfProd_and_eq_mul_pmfProb {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β)
    (p : α → Prop) (q : β → Prop)
    [DecidablePred p] [DecidablePred q] :
    pmfProb (pmfProd μ ν) (fun x : α × β => p x.1 ∧ q x.2) =
      pmfProb μ p * pmfProb ν q := by
  classical
  unfold pmfProb
  rw [pmfExp_pmfProd_eq_pairExp]
  exact pmfPairExp_indicator_and_eq_mul_pmfProb μ ν p q

/--
Under an independent product PMF, conditioning on a positive product event
`p(first) ∧ q(second)` leaves first-coordinate conditional probabilities equal
to the conditional probability under the first marginal given `p`.
-/
theorem pmfConditionalProb_pmfProd_fst_eq
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β)
    (p event : α → Prop) (q : β → Prop)
    [DecidablePred p] [DecidablePred event] [DecidablePred q]
    (hp_pos : 0 < pmfProb μ p)
    (hq_pos : 0 < pmfProb ν q) :
    pmfConditionalProb (pmfProd μ ν)
        (fun x : α × β => p x.1 ∧ q x.2)
        (fun x : α × β => event x.1) =
      pmfConditionalProb μ p event := by
  classical
  have hcondition_pos :
      0 <
        pmfProb (pmfProd μ ν)
          (fun x : α × β => p x.1 ∧ q x.2) := by
    rw [pmfProb_pmfProd_and_eq_mul_pmfProb μ ν p q]
    exact mul_pos hp_pos hq_pos
  rw [pmfConditionalProb_eq_inter_div_of_pos
    (pmfProd μ ν)
    (fun x : α × β => p x.1 ∧ q x.2)
    (fun x : α × β => event x.1)
    hcondition_pos]
  rw [pmfConditionalProb_eq_inter_div_of_pos μ p event hp_pos]
  have hnum :
      pmfProb (pmfProd μ ν)
          (fun x : α × β =>
            (p x.1 ∧ q x.2) ∧ event x.1) =
        pmfProb μ (fun a => p a ∧ event a) * pmfProb ν q := by
    calc
      pmfProb (pmfProd μ ν)
          (fun x : α × β =>
            (p x.1 ∧ q x.2) ∧ event x.1)
          =
        pmfProb (pmfProd μ ν)
          (fun x : α × β => (p x.1 ∧ event x.1) ∧ q x.2) := by
          refine pmfProb_congr _ ?_
          intro x
          tauto
      _ = pmfProb μ (fun a => p a ∧ event a) * pmfProb ν q := by
          rw [pmfProb_pmfProd_and_eq_mul_pmfProb
            μ ν (fun a => p a ∧ event a) q]
  have hden :
      pmfProb (pmfProd μ ν)
          (fun x : α × β => p x.1 ∧ q x.2) =
        pmfProb μ p * pmfProb ν q :=
    pmfProb_pmfProd_and_eq_mul_pmfProb μ ν p q
  rw [hnum, hden]
  field_simp [hp_pos.ne', hq_pos.ne']

/-- Under an independent product PMF, a first-coordinate event has its marginal probability. -/
theorem pmfProb_pmfProd_fst_eq {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β)
    (p : α → Prop) [DecidablePred p] :
    pmfProb (pmfProd μ ν) (fun x : α × β => p x.1) =
      pmfProb μ p := by
  classical
  unfold pmfProb
  rw [pmfExp_pmfProd_eq_pairExp]
  exact pmfPairExp_ignore_right μ ν (fun a => if p a then (1 : ℝ) else 0)

/-- Under an independent product PMF, a second-coordinate event has its marginal probability. -/
theorem pmfProb_pmfProd_snd_eq {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β)
    (q : β → Prop) [DecidablePred q] :
    pmfProb (pmfProd μ ν) (fun x : α × β => q x.2) =
      pmfProb ν q := by
  classical
  unfold pmfProb
  rw [pmfExp_pmfProd_eq_pairExp]
  exact pmfPairExp_ignore_left μ ν (fun b => if q b then (1 : ℝ) else 0)

/--
Conditioning an independent finite product on a positive-probability event of
the first coordinate leaves every second-coordinate event at its marginal
probability.  This is the finite one-step post-history independence fact used
by stopped iid constructions.
-/
theorem pmfConditionalProb_pmfProd_snd_eq_pmfProb_of_fst
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β)
    (past : α → Prop) (future : β → Prop)
    [DecidablePred past] [DecidablePred future]
    (hpast_pos : 0 < pmfProb μ past) :
    pmfConditionalProb (pmfProd μ ν)
        (fun x : α × β => past x.1)
        (fun x : α × β => future x.2) =
      pmfProb ν future := by
  classical
  have hcondition :
      pmfProb (pmfProd μ ν) (fun x : α × β => past x.1) =
        pmfProb μ past :=
    pmfProb_pmfProd_fst_eq μ ν past
  have hcondition_pos :
      0 < pmfProb (pmfProd μ ν) (fun x : α × β => past x.1) := by
    rw [hcondition]
    exact hpast_pos
  have hinter :
      pmfProb (pmfProd μ ν)
          (fun x : α × β => past x.1 ∧ future x.2) =
        pmfProb μ past * pmfProb ν future := by
    rw [pmfProb_pmfProd_and_eq_mul_pmfProb]
  rw [pmfConditionalProb_eq_inter_div_of_pos
    (pmfProd μ ν)
    (fun x : α × β => past x.1)
    (fun x : α × β => future x.2)
    hcondition_pos]
  rw [hinter, hcondition]
  field_simp [hpast_pos.ne']

/--
If a second-coordinate event has probability one, then a product event that
agrees with a first-coordinate event on that full-probability slice has the
first marginal probability.
-/
theorem pmfProb_pmfProd_eq_fst_of_snd_prob_one {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β)
    (p : α → Prop) (q : β → Prop) (r : α × β → Prop)
    [DecidablePred p] [DecidablePred q] [DecidablePred r]
    (hq_one : pmfProb ν q = 1)
    (hr : ∀ a b, q b → (r (a, b) ↔ p a)) :
    pmfProb (pmfProd μ ν) r = pmfProb μ p := by
  classical
  let prod := pmfProd μ ν
  let good : α × β → Prop := fun x => q x.2
  have hsplit :=
    pmfProb_eq_inter_add_inter_not prod r good
  have hbad_zero :
      pmfProb prod (fun x => r x ∧ ¬ good x) = 0 := by
    have hbad_le :
        pmfProb prod (fun x => r x ∧ ¬ good x) ≤
          pmfProb prod (fun x => ¬ good x) :=
      pmfProb_le_of_imp prod (fun x => r x ∧ ¬ good x)
        (fun x => ¬ good x) (fun x hx => hx.2)
    have hnot_good :
        pmfProb prod (fun x => ¬ good x) = 0 := by
      rw [pmfProb_pmfProd_snd_eq μ ν (fun b => ¬ q b)]
      rw [pmfProb_compl ν q, hq_one]
      norm_num
    exact le_antisymm (hbad_le.trans (le_of_eq hnot_good))
      (pmfProb_nonneg prod (fun x => r x ∧ ¬ good x))
  have hgood_eq :
      pmfProb prod (fun x => r x ∧ good x) = pmfProb μ p := by
    have hcongr :
        pmfProb prod (fun x => r x ∧ good x) =
          pmfProb prod (fun x => p x.1 ∧ q x.2) :=
      pmfProb_congr prod (by
        intro x
        constructor
        · intro hx
          exact ⟨(hr x.1 x.2 hx.2).1 hx.1, hx.2⟩
        · intro hx
          exact ⟨(hr x.1 x.2 hx.2).2 hx.1, hx.2⟩)
    rw [hcongr, pmfProb_pmfProd_and_eq_mul_pmfProb μ ν p q, hq_one]
    ring
  rw [hsplit, hbad_zero, hgood_eq, add_zero]

/--
If a first-coordinate event has probability one, then a product event that
agrees with a second-coordinate event on that full-probability slice has the
second marginal probability.
-/
theorem pmfProb_pmfProd_eq_snd_of_fst_prob_one {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β)
    (p : α → Prop) (q : β → Prop) (r : α × β → Prop)
    [DecidablePred p] [DecidablePred q] [DecidablePred r]
    (hp_one : pmfProb μ p = 1)
    (hr : ∀ a b, p a → (r (a, b) ↔ q b)) :
    pmfProb (pmfProd μ ν) r = pmfProb ν q := by
  classical
  let prod := pmfProd μ ν
  let good : α × β → Prop := fun x => p x.1
  have hsplit :=
    pmfProb_eq_inter_add_inter_not prod r good
  have hbad_zero :
      pmfProb prod (fun x => r x ∧ ¬ good x) = 0 := by
    have hbad_le :
        pmfProb prod (fun x => r x ∧ ¬ good x) ≤
          pmfProb prod (fun x => ¬ good x) :=
      pmfProb_le_of_imp prod (fun x => r x ∧ ¬ good x)
        (fun x => ¬ good x) (fun x hx => hx.2)
    have hnot_good :
        pmfProb prod (fun x => ¬ good x) = 0 := by
      rw [pmfProb_pmfProd_fst_eq μ ν (fun a => ¬ p a)]
      rw [pmfProb_compl μ p, hp_one]
      norm_num
    exact le_antisymm (hbad_le.trans (le_of_eq hnot_good))
      (pmfProb_nonneg prod (fun x => r x ∧ ¬ good x))
  have hgood_eq :
      pmfProb prod (fun x => r x ∧ good x) = pmfProb ν q := by
    have hcongr :
        pmfProb prod (fun x => r x ∧ good x) =
          pmfProb prod (fun x => p x.1 ∧ q x.2) :=
      pmfProb_congr prod (by
        intro x
        constructor
        · intro hx
          exact ⟨hx.2, (hr x.1 x.2 hx.2).1 hx.1⟩
        · intro hx
          exact ⟨(hr x.1 x.2 hx.1).2 hx.2, hx.1⟩)
    rw [hcongr, pmfProb_pmfProd_and_eq_mul_pmfProb μ ν p q, hp_one]
    ring
  rw [hsplit, hbad_zero, hgood_eq, add_zero]

/-- The expectation of a separable product factors under independent draws. -/
theorem pmfPairExp_mul_separable {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (f : α → ℝ) (g : β → ℝ) :
    pmfPairExp μ ν (fun a b => f a * g b) =
      pmfExp μ f * pmfExp ν g := by
  classical
  unfold pmfPairExp pmfExp
  calc
    ∑ a : α, (μ a).toReal * (∑ b : β, (ν b).toReal * (f a * g b))
        =
        ∑ a : α, (μ a).toReal * (f a * ∑ b : β, (ν b).toReal * g b) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          congr 1
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro b _
          ring
    _ =
        (∑ a : α, (μ a).toReal * f a) *
          (∑ b : β, (ν b).toReal * g b) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro a _
          ring

end EconCSLib
