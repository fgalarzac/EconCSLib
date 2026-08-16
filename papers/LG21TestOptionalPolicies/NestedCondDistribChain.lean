import Mathlib.Probability.Kernel.CondDistrib

/-!
# Nested regular conditional-distribution chain rule

This module is source-neutral measure theory.  It records the almost-everywhere
chain factorization of the conditional law of a pair `(score, skill)` given a
base observation.  It makes no claim about any paper model, posterior formula,
or equilibrium interpretation.

The theorem is deliberately stated with the actual base marginal as its
almost-everywhere measure.  Regular conditional distributions are not
canonically determined on null base fibres.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ProbabilityTheory

/--
For a finite population law, conditioning `(score, skill)` on `base` factors
almost everywhere by first conditioning `score` on `base`, then conditioning
`skill` on the joint observation `(base, score)`.

The right-hand side has target `Score × Skill`; `Kernel.compProd` supplies the
necessary sequential product and the proof accounts explicitly for the
associator between `((base, score), skill)` and `(base, (score, skill))`.
-/
theorem condDistrib_score_skill_chain_ae
    {Ω Base Score Skill : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Base]
    [MeasurableSpace Score] [StandardBorelSpace Score] [Nonempty Score]
    [MeasurableSpace Skill] [StandardBorelSpace Skill] [Nonempty Skill]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (base : Ω → Base) (score : Ω → Score) (skill : Ω → Skill)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill) :
    condDistrib (fun ω => (score ω, skill ω)) base μ =ᵐ[μ.map base]
      condDistrib score base μ ⊗ₖ
        condDistrib skill (fun ω => (base ω, score ω)) μ := by
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    hbase (hscore.prodMk hskill)
  calc
    μ.map (fun ω => (base ω, (score ω, skill ω))) =
        (μ.map (fun ω => ((base ω, score ω), skill ω))).map
          MeasurableEquiv.prodAssoc := by
      rw [Measure.map_map]
      · rfl
      · exact MeasurableEquiv.measurable _
      · exact (hbase.prodMk hscore).prodMk hskill
    _ =
        ((μ.map (fun ω => (base ω, score ω))) ⊗ₘ
          condDistrib skill (fun ω => (base ω, score ω)) μ).map
            MeasurableEquiv.prodAssoc := by
      rw [compProd_map_condDistrib hskill.aemeasurable]
    _ =
        ((μ.map base ⊗ₘ condDistrib score base μ) ⊗ₘ
          condDistrib skill (fun ω => (base ω, score ω)) μ).map
            MeasurableEquiv.prodAssoc := by
      rw [compProd_map_condDistrib hscore.aemeasurable]
    _ = μ.map base ⊗ₘ (condDistrib score base μ ⊗ₖ
          condDistrib skill (fun ω => (base ω, score ω)) μ) := by
      rw [Measure.compProd_assoc']

end

end LG21TestOptionalPolicies
