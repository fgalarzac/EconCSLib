import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-!
# Analytic rigidity tools for LG21's Gaussian test model

The report-required branch of LG21 Theorem 3.2 reduces to a Gaussian
convolution-identification question.  This module contains only reusable
measure-theoretic infrastructure; it deliberately does not assert the paper
theorem or add any policy-model assumptions.

The central route is:

1. turn a signed density into its positive and negative finite measures;
2. identify those measures from their moment-generating functions by analytic
   continuation; and
3. recover almost-everywhere equality of the densities.

The remaining source-specific bridge is to turn equality of the Gaussian
convolution on the relevant set of latent skills into the MGF equality assumed
by `lg21_ae_eq_zero_of_pos_neg_density_mgf_eq` below.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal MeasureTheory ProbabilityTheory Topology

/--
Entire complex-analytic functions which agree on a positive-mass set for an
atomless measure agree everywhere.  This packages the positive-mass-to-
accumulation-point bridge used when a Gaussian convolution identity is first
known only for a positive-measure set of latent skills.
-/
theorem lg21_entire_analytic_eq_of_pos_measure_eq
    {μ : Measure ℂ} [NoAtoms μ]
    {f g : ℂ → ℂ} [TopologicalSpace.SeparableSpace {z : ℂ // f z = g z}]
    (hf : AnalyticOnNhd ℂ f Set.univ)
    (hg : AnalyticOnNhd ℂ g Set.univ)
    (hpositive : 0 < μ {z | f z = g z}) :
    f = g := by
  obtain ⟨z, hz⟩ := exists_accPt_of_noAtoms hpositive
  apply AnalyticOnNhd.eq_of_frequently_eq hf hg
  exact (accPt_iff_frequently_nhdsNE.mp hz).mono fun _ hEq ↦ hEq

/-- Matching MGFs of finite measures also determine their common zero status. -/
theorem lg21_measure_zero_iff_of_mgf_eq
    {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmgf : mgf id μ = mgf id ν) :
    μ = 0 ↔ ν = 0 := by
  constructor
  · intro hμ
    have hν_zero_mgf : mgf id ν 0 = 0 := by
      simpa [hμ] using (congrFun hmgf 0).symm
    apply Measure.measure_univ_eq_zero.mp
    exact (measureReal_eq_zero_iff (by finiteness)).mp (by
      simpa only [mgf_zero'] using hν_zero_mgf)
  · intro hν
    have hμ_zero_mgf : mgf id μ 0 = 0 := by
      simpa [hν] using congrFun hmgf 0
    apply Measure.measure_univ_eq_zero.mp
    exact (measureReal_eq_zero_iff (by finiteness)).mp (by
      simpa only [mgf_zero'] using hμ_zero_mgf)

/--
Finite real measures with matching moment-generating functions are equal when
one measure has every real exponential moment.  The matching MGF and common
zero/nonzero status make Mathlib identify the other measure's integrability
domain automatically.  The proof deliberately
uses `complexMGF`: equality on the real axis analytically continues to the
whole complex plane, after which Mathlib's complex-MGF extensionality theorem
identifies the measures.
-/
theorem lg21_measure_eq_of_mgf_eq_of_all_real_exp_integrable
    {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ_exp : ∀ t : ℝ, Integrable (fun x : ℝ ↦ rexp (t * x)) μ)
    (hmgf : mgf id μ = mgf id ν) :
    μ = ν := by
  apply Measure.ext_of_complexMGF_id_eq
  have hμ_univ : integrableExpSet id μ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro t
    exact hμ_exp t
  have h_eq_on := eqOn_complexMGF_of_mgf' (X := id) (Y := id)
    (μ := μ) (μ' := ν) hmgf (lg21_measure_zero_iff_of_mgf_eq hmgf)
  rw [hμ_univ] at h_eq_on
  exact funext fun z ↦ h_eq_on (by simp)

/-!
## Signed-density reduction

For a real-valued density `f`, the two definitions below are the positive and
negative density measures.  They are kept as honest positive measures so the
complex-MGF extensionality theorem applies directly.
-/

/-- Positive-density measure associated with a real-valued function. -/
def lg21PositiveDensityMeasure (μ : Measure ℝ) (f : ℝ → ℝ) : Measure ℝ :=
  μ.withDensity (fun x ↦ ENNReal.ofReal (max (f x) 0))

/-- Negative-density measure associated with a real-valued function. -/
def lg21NegativeDensityMeasure (μ : Measure ℝ) (f : ℝ → ℝ) : Measure ℝ :=
  μ.withDensity (fun x ↦ ENNReal.ofReal (max (-f x) 0))

/-- Pointwise reconstruction of a real number from its positive and negative parts. -/
theorem lg21_sub_pos_neg_eq_self (x : ℝ) :
    max x 0 - max (-x) 0 = x := by
  exact max_zero_sub_eq_self x

/--
If the positive and negative density measures of `f` are equal, then `f`
vanishes almost everywhere.  This is the final signed-measure step in a
Gaussian/Weierstrass rigidity proof.
-/
theorem lg21_ae_eq_zero_of_pos_neg_density_measure_eq
    {μ : Measure ℝ} [SigmaFinite μ]
    (f : ℝ → ℝ)
    (hf : AEMeasurable f μ)
    (hmeasure : lg21PositiveDensityMeasure μ f = lg21NegativeDensityMeasure μ f) :
    f =ᵐ[μ] 0 := by
  have hf_pos : AEMeasurable (fun x ↦ ENNReal.ofReal (max (f x) 0)) μ := by
    fun_prop
  have hf_neg : AEMeasurable (fun x ↦ ENNReal.ofReal (max (-f x) 0)) μ := by
    fun_prop
  have hdensity :
      (fun x ↦ ENNReal.ofReal (max (f x) 0)) =ᵐ[μ]
        fun x ↦ ENNReal.ofReal (max (-f x) 0) := by
    apply (withDensity_eq_iff_of_sigmaFinite hf_pos hf_neg).mp
    exact hmeasure
  filter_upwards [hdensity] with x hx
  have hx_real : max (f x) 0 = max (-f x) 0 := by
    exact (ENNReal.ofReal_eq_ofReal_iff
      (le_max_right _ _) (le_max_right _ _)).mp hx
  change f x = 0
  rw [← lg21_sub_pos_neg_eq_self (f x), hx_real, sub_self]

/--
The reusable analytic conclusion: when the positive and negative density
measures have equal MGFs and the positive measure has every real exponential
moment, the signed density is zero almost everywhere.  The MGF equality is
the exact proof obligation left by the Gaussian convolution layer.
-/
theorem lg21_ae_eq_zero_of_pos_neg_density_mgf_eq
    {μ : Measure ℝ} [SigmaFinite μ]
    (f : ℝ → ℝ)
    (hf : AEMeasurable f μ)
    (hpos_finite : IsFiniteMeasure (lg21PositiveDensityMeasure μ f))
    (hneg_finite : IsFiniteMeasure (lg21NegativeDensityMeasure μ f))
    (hpos_exp : ∀ t : ℝ,
      Integrable (fun x : ℝ ↦ rexp (t * x))
        (lg21PositiveDensityMeasure μ f))
    (hmgf : mgf id (lg21PositiveDensityMeasure μ f) =
      mgf id (lg21NegativeDensityMeasure μ f)) :
    f =ᵐ[μ] 0 := by
  letI : IsFiniteMeasure (lg21PositiveDensityMeasure μ f) := hpos_finite
  letI : IsFiniteMeasure (lg21NegativeDensityMeasure μ f) := hneg_finite
  apply lg21_ae_eq_zero_of_pos_neg_density_measure_eq f hf
  exact lg21_measure_eq_of_mgf_eq_of_all_real_exp_integrable
    hpos_exp hmgf

end

end LG21TestOptionalPolicies
