import LG21TestOptionalPolicies.ObservedAccessOptionalSection4Bridge

/-!
# Canonical source-law policy for LG21 Proposition 4.2

This module packages the Section 4 Gaussian PBO policy as the paper's full
`LG21SourceLawPolicySurface`.  Its Definition 2 fields are literal conditional
output laws at a fixed latent skill and non-test feature profile.  In
particular, it does not obtain those fields by disintegrating an aggregate
realized-output law, and it makes no claim about a voluntary profile's actions.

The access branch is the total Gaussian PBO rule after the actual score is
observed.  The no-access branch is any Markov kernel indexed only by the
non-test profile, exactly matching the information restriction used in the
source proof.  The remaining surface fields are the corresponding conditional
or marginal laws of the same total policy.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory

/--
The total observed-access Gaussian PBO policy expressed on a supplied
policy-state index.  This is a fixed-fibre policy-law construction, not by
itself a source equilibrium: a source-facing route must separately establish
that its index is realized by the selected action/PBO model.

* Fixed `(base, skill)` access output draws the actual score and applies PBO.
* Fixed-base no-access output is the arbitrary base-only policy kernel.
* Observable and demographic fields are the same policy's Gaussian
  conditional and marginal laws.
-/
def lg21P42CanonicalPBOPolicySourceLawSurfaceAt
    {Base : Type*} [MeasurableSpace Base]
    (PolicyState : Type*)
    (S : LG21GaussianPBOResamplingSource Base)
    (noAccessEstimateKernel : Kernel Base ℝ)
    [IsMarkovKernel noAccessEstimateKernel] :
    LG21SourceLawPolicySurface ℝ Base ℝ (Measure ℝ) where
  Equilibrium := PolicyState
  latentAccessLaw := fun _ skill base =>
    lg21P42AccessEstimateKernel
      (lg21P42ObservedScoreModelOfD6Source S noAccessEstimateKernel)
      (base, skill)
  latentNoAccessLaw := fun _ _ base => noAccessEstimateKernel base
  observableAccessLaw := fun _ base => lg21D6ActualAccessEstimateKernel S base
  observableNoAccessLaw := fun _ base => noAccessEstimateKernel base
  demographicAccessLaw := fun _ => lg21D6ActualAccessEstimateLaw S
  demographicNoAccessLaw := fun _ => Measure.bind S.baseLaw noAccessEstimateKernel
  baseOnlyLaw := fun _ base => noAccessEstimateKernel base
  fullFeatureLaw := fun _ base score =>
    Measure.dirac (lg21D6GaussianPBOEstimate S (base, score))

/--
The policy-fibre information-gap calculation.  Once one actual policy state
is supplied, the Gaussian PBO access law cannot equal one base-only no-access
law at every latent skill.  This theorem intentionally does not claim that
`PolicyState` is a Definition 1 equilibrium; source-facing bridges provide
that evidence separately.
-/
theorem lg21P42CanonicalPBOPolicyLaw_not_latent_skill_fair_of_state
    {Base : Type*} [MeasurableSpace Base]
    {PolicyState : Type*} (state : PolicyState)
    (S : LG21GaussianPBOResamplingSource Base)
    (noAccessEstimateKernel : Kernel Base ℝ)
    [IsMarkovKernel noAccessEstimateKernel]
    (base : Base) {skillLow skillHigh : ℝ} (hskill : skillLow < skillHigh) :
    ¬ lg21SourceLawLatentSkillFair
      (lg21P42CanonicalPBOPolicySourceLawSurfaceAt PolicyState S
        noAccessEstimateKernel) := by
  exact paper_proposition4_2_actual_observed_score_source_law_not_latent_skill_fair
    (lg21P42ObservedScoreModelOfD6Source S noAccessEstimateKernel) state
    (by
      intro skill publicBase
      rfl)
    (by
      intro skill publicBase
      rfl)
    base hskill

/-- The single-state version is retained only as an auxiliary policy-fibre
calculation.  `Unit` here denotes one policy state, not a source equilibrium.
Use the active-branch source realization for the paper-facing Proposition 4.2
route. -/
def lg21P42CanonicalPBOPolicyLawSurface
    {Base : Type*} [MeasurableSpace Base]
    (S : LG21GaussianPBOResamplingSource Base)
    (noAccessEstimateKernel : Kernel Base ℝ)
    [IsMarkovKernel noAccessEstimateKernel] :
    LG21SourceLawPolicySurface ℝ Base ℝ (Measure ℝ) :=
  lg21P42CanonicalPBOPolicySourceLawSurfaceAt Unit S noAccessEstimateKernel

theorem lg21P42CanonicalPBOPolicyLaw_not_latent_skill_fair
    {Base : Type*} [MeasurableSpace Base]
    (S : LG21GaussianPBOResamplingSource Base)
    (noAccessEstimateKernel : Kernel Base ℝ)
    [IsMarkovKernel noAccessEstimateKernel]
    (base : Base) {skillLow skillHigh : ℝ} (hskill : skillLow < skillHigh) :
    ¬ lg21SourceLawLatentSkillFair
      (lg21P42CanonicalPBOPolicyLawSurface S noAccessEstimateKernel) := by
  exact lg21P42CanonicalPBOPolicyLaw_not_latent_skill_fair_of_state () S
    noAccessEstimateKernel base hskill

end

end LG21TestOptionalPolicies
