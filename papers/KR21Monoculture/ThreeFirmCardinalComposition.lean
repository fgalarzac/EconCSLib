import KR21Monoculture.ThreeFirmMallowsProductLawBridge
import KR21Monoculture.ThreeFirmUniformCardinalBridge

open MeasureTheory
open scoped BigOperators

namespace KR21Monoculture

/-! The named finite source types carry the discrete sigma-algebra in this
module, so the PMF-to-measure and product-measure constructions below have
their intended finite measurable structure. -/
local instance : MeasurableSpace SourceFourRanking := ⊤
local instance : MeasurableSingletonClass SourceFourRanking := ⟨fun _ => trivial⟩
local instance : MeasurableSpace SourceFirmOrder := ⊤
local instance : MeasurableSingletonClass SourceFirmOrder := ⟨fun _ => trivial⟩

/-!
# Sequential cardinal composition for the KR21 three-firm finite instance

The finite product-law bridge provides the exact distribution of ranking and
arrival inputs.  The Uniform-cardinal bridge proves the expectation identity
for any deterministic finite true-rank selector.  This module supplies that
selector for the actual three-step sequential choice rule and composes the two
facts.  It does not identify this explicitly constructed product experiment
with every detail of the published simulation.
-/

/-- The true-rank selected by labeled firm `0` after the three sequential
choices determined by fixed rankings and a fixed arrival order. -/
def sourceFocalSelectedCandidate (usesAlgorithm : SourceThreeFirm → Bool)
    (algorithm : SourceFourRanking)
    (human : SourceThreeFirm → SourceFourRanking)
    (order : SourceFirmOrder) : SourceFourCandidate :=
  let ranking : SourceThreeFirm → SourceFourRanking := fun firm =>
    if usesAlgorithm firm then algorithm else human firm
  let c0 := sourceBestAvailable (ranking (order 0)) ∅
  let c1 := sourceBestAvailable (ranking (order 1)) {c0}
  let c2 := sourceBestAvailable (ranking (order 2)) {c0, c1}
  if order 0 = 0 then c0
  else if order 1 = 0 then c1
  else c2

/-- The existing rank-mean payoff is precisely the true-rank order-statistic
table evaluated at the deterministic sequential focal selection. -/
theorem sourceFocalUtility_eq_selectedRankMean
    (usesAlgorithm : SourceThreeFirm → Bool)
    (algorithm : SourceFourRanking)
    (human : SourceThreeFirm → SourceFourRanking)
    (order : SourceFirmOrder) :
    sourceFocalUtility usesAlgorithm algorithm human order =
      sourceExpectedOrderStatisticValue
        (sourceFocalSelectedCandidate usesAlgorithm algorithm human order) := by
  by_cases hfirst : order 0 = 0
  · simp [sourceFocalUtility, sourceFocalSelectedCandidate, hfirst]
  · by_cases hsecond : order 1 = 0
    · simp [sourceFocalUtility, sourceFocalSelectedCandidate, hfirst, hsecond]
    · simp [sourceFocalUtility, sourceFocalSelectedCandidate, hfirst, hsecond]

/-! ## Shared-algorithm AAA product experiment -/

/-- The deterministic true-rank selected by firm `0` in the actual finite
shared-algorithm ranking/arrival experiment.  The auxiliary ranking map is
the shared algorithm itself, matching the direct finite conditional model. -/
def sourceAAASequentialFocalCandidate
    (outcome : SourceFourRanking × SourceFirmOrder) : SourceFourCandidate :=
  sourceFocalSelectedCandidate sourceProfileAAA outcome.1
    (sourceSharedAlgorithmRankings outcome.1) outcome.2

/-- At AAA, the sequential selector's rank-table value is the existing direct
rank-mean payoff pointwise. -/
theorem sourceAAASequentialFocalCandidate_rankMean
    (algorithm : SourceFourRanking) (order : SourceFirmOrder) :
    sourceExpectedOrderStatisticValue
      (sourceAAASequentialFocalCandidate (algorithm, order)) =
      sourceDirectRankMeanConditionalAAA algorithm order := by
  simpa [sourceAAASequentialFocalCandidate] using
    (sourceFocalUtility_eq_selectedRankMean sourceProfileAAA algorithm
      (sourceSharedAlgorithmRankings algorithm) order).symm

/-- The explicitly constructed shared-AAA ranking/arrival product law,
independent of the four iid Uniform cardinal values. -/
noncomputable def sourceAAACardinalProductLaw :
    Measure ((SourceFourRanking × SourceFirmOrder) × (Fin 4 → ℝ)) :=
  sourceAAAProductLaw.toMeasure.prod sourceFourUniformValueLaw

/-- Firm `0`'s realized cardinal utility in that explicit product experiment. -/
noncomputable def sourceAAACardinalUtility
    (outcome : (SourceFourRanking × SourceFirmOrder) × (Fin 4 → ℝ)) : ℝ :=
  sourceFourSelectedUniformUtilityOf sourceAAASequentialFocalCandidate outcome

/-- The shared-AAA cardinal product experiment has expected focal utility
equal to the finite PMF-weighted sequential rank-mean table. -/
theorem sourceAAACardinalUtility_integral_eq_weighted_rankMean :
    (∫ outcome, sourceAAACardinalUtility outcome ∂sourceAAACardinalProductLaw) =
      ∑ outcome : SourceFourRanking × SourceFirmOrder,
        (sourceAAAProductLaw outcome).toReal *
          (sourceExpectedOrderStatisticValue
            (sourceAAASequentialFocalCandidate outcome) : ℝ) := by
  exact sourceFourSelectedUniformUtilityOf_integral_eq_weighted_table
    sourceAAAProductLaw sourceAAASequentialFocalCandidate

/-- The explicitly constructed shared-AAA cardinal product experiment has
expected focal utility exactly equal to the existing actual finite PMF
rank-mean expectation. -/
theorem sourceAAACardinalUtility_integral_eq_productLawExpectation :
    (∫ outcome, sourceAAACardinalUtility outcome ∂sourceAAACardinalProductLaw) =
      sourceAAAProductLawExpectation := by
  rw [sourceAAACardinalUtility_integral_eq_weighted_rankMean]
  unfold sourceAAAProductLawExpectation
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro algorithm _
  apply Finset.sum_congr rfl
  intro order _
  rw [sourceAAASequentialFocalCandidate_rankMean]

/-- Combining the cardinal composition with the already checked finite
Mallows/arrival calculation gives the exact rational expected cardinal payoff
for the explicit shared-AAA product experiment. -/
theorem sourceAAACardinalUtility_integral_eq_cast_direct :
    (∫ outcome, sourceAAACardinalUtility outcome ∂sourceAAACardinalProductLaw) =
      ((sourceDirectRankMeanExpectedAAA : ℚ) : ℝ) := by
  rw [sourceAAACardinalUtility_integral_eq_productLawExpectation,
    sourceAAAProductLawExpectation_eq_cast_direct]

/-! ## One-human mixed product experiments -/

/-- The sequential focal true-rank selector at the HAA profile. -/
def sourceHAASequentialFocalCandidate
    (outcome : (SourceFourRanking × SourceFourRanking) × SourceFirmOrder) :
    SourceFourCandidate :=
  sourceFocalSelectedCandidate sourceProfileHAA outcome.1.1
    (sourceHumanRankings outcome.1.2 .r0123 .r0123) outcome.2

/-- The sequential focal true-rank selector at the AAH profile. -/
def sourceAAHSequentialFocalCandidate
    (outcome : (SourceFourRanking × SourceFourRanking) × SourceFirmOrder) :
    SourceFourCandidate :=
  sourceFocalSelectedCandidate sourceProfileAAH outcome.1.1
    (sourceHumanRankings .r0123 .r0123 outcome.1.2) outcome.2

theorem sourceHAASequentialFocalCandidate_rankMean
    (algorithm human : SourceFourRanking) (order : SourceFirmOrder) :
    sourceExpectedOrderStatisticValue
      (sourceHAASequentialFocalCandidate ((algorithm, human), order)) =
      sourceFocalUtility sourceProfileHAA algorithm
        (sourceHumanRankings human .r0123 .r0123) order := by
  simpa [sourceHAASequentialFocalCandidate] using
    (sourceFocalUtility_eq_selectedRankMean sourceProfileHAA algorithm
      (sourceHumanRankings human .r0123 .r0123) order).symm

theorem sourceAAHSequentialFocalCandidate_rankMean
    (algorithm human : SourceFourRanking) (order : SourceFirmOrder) :
    sourceExpectedOrderStatisticValue
      (sourceAAHSequentialFocalCandidate ((algorithm, human), order)) =
      sourceFocalUtility sourceProfileAAH algorithm
        (sourceHumanRankings .r0123 .r0123 human) order := by
  simpa [sourceAAHSequentialFocalCandidate] using
    (sourceFocalUtility_eq_selectedRankMean sourceProfileAAH algorithm
      (sourceHumanRankings .r0123 .r0123 human) order).symm

/-- The explicit HAA finite-ranking × iid-Uniform-cardinal product law. -/
noncomputable def sourceHAACardinalProductLaw :
    Measure (((SourceFourRanking × SourceFourRanking) × SourceFirmOrder) ×
      (Fin 4 → ℝ)) :=
  sourceOneHumanProductLaw.toMeasure.prod sourceFourUniformValueLaw

/-- The explicit AAH finite-ranking × iid-Uniform-cardinal product law. -/
noncomputable def sourceAAHCardinalProductLaw :
    Measure (((SourceFourRanking × SourceFourRanking) × SourceFirmOrder) ×
      (Fin 4 → ℝ)) :=
  sourceOneHumanProductLaw.toMeasure.prod sourceFourUniformValueLaw

noncomputable def sourceHAACardinalUtility
    (outcome : ((SourceFourRanking × SourceFourRanking) × SourceFirmOrder) ×
      (Fin 4 → ℝ)) : ℝ :=
  sourceFourSelectedUniformUtilityOf sourceHAASequentialFocalCandidate outcome

noncomputable def sourceAAHCardinalUtility
    (outcome : ((SourceFourRanking × SourceFourRanking) × SourceFirmOrder) ×
      (Fin 4 → ℝ)) : ℝ :=
  sourceFourSelectedUniformUtilityOf sourceAAHSequentialFocalCandidate outcome

theorem sourceHAACardinalUtility_integral_eq_productLawExpectation :
    (∫ outcome, sourceHAACardinalUtility outcome ∂sourceHAACardinalProductLaw) =
      sourceHAAProductLawExpectation := by
  unfold sourceHAACardinalUtility sourceHAACardinalProductLaw
  rw [sourceFourSelectedUniformUtilityOf_integral_eq_weighted_table]
  calc
    (∑ outcome : (SourceFourRanking × SourceFourRanking) × SourceFirmOrder,
      (sourceOneHumanProductLaw outcome).toReal *
        (sourceExpectedOrderStatisticValue
          (sourceHAASequentialFocalCandidate outcome) : ℝ)) =
        ∑ algorithm : SourceFourRanking,
          ∑ human : SourceFourRanking,
            ∑ order : SourceFirmOrder,
              (sourceOneHumanProductLaw ((algorithm, human), order)).toReal *
                (sourceExpectedOrderStatisticValue
                  (sourceHAASequentialFocalCandidate ((algorithm, human), order)) : ℝ) := by
          rw [Fintype.sum_prod_type]
          simp_rw [Fintype.sum_prod_type]
    _ = ∑ algorithm : SourceFourRanking,
          ∑ order : SourceFirmOrder,
            ∑ human : SourceFourRanking,
              (sourceOneHumanProductLaw ((algorithm, human), order)).toReal *
                (sourceExpectedOrderStatisticValue
                  (sourceHAASequentialFocalCandidate ((algorithm, human), order)) : ℝ) := by
          apply Finset.sum_congr rfl
          intro algorithm _
          rw [Finset.sum_comm]
    _ = sourceHAAProductLawExpectation := by
          unfold sourceHAAProductLawExpectation
          apply Finset.sum_congr rfl
          intro algorithm _
          apply Finset.sum_congr rfl
          intro order _
          apply Finset.sum_congr rfl
          intro human _
          rw [sourceHAASequentialFocalCandidate_rankMean]

theorem sourceAAHCardinalUtility_integral_eq_productLawExpectation :
    (∫ outcome, sourceAAHCardinalUtility outcome ∂sourceAAHCardinalProductLaw) =
      sourceAAHProductLawExpectation := by
  unfold sourceAAHCardinalUtility sourceAAHCardinalProductLaw
  rw [sourceFourSelectedUniformUtilityOf_integral_eq_weighted_table]
  calc
    (∑ outcome : (SourceFourRanking × SourceFourRanking) × SourceFirmOrder,
      (sourceOneHumanProductLaw outcome).toReal *
        (sourceExpectedOrderStatisticValue
          (sourceAAHSequentialFocalCandidate outcome) : ℝ)) =
        ∑ algorithm : SourceFourRanking,
          ∑ human : SourceFourRanking,
            ∑ order : SourceFirmOrder,
              (sourceOneHumanProductLaw ((algorithm, human), order)).toReal *
                (sourceExpectedOrderStatisticValue
                  (sourceAAHSequentialFocalCandidate ((algorithm, human), order)) : ℝ) := by
          rw [Fintype.sum_prod_type]
          simp_rw [Fintype.sum_prod_type]
    _ = ∑ algorithm : SourceFourRanking,
          ∑ order : SourceFirmOrder,
            ∑ human : SourceFourRanking,
              (sourceOneHumanProductLaw ((algorithm, human), order)).toReal *
                (sourceExpectedOrderStatisticValue
                  (sourceAAHSequentialFocalCandidate ((algorithm, human), order)) : ℝ) := by
          apply Finset.sum_congr rfl
          intro algorithm _
          rw [Finset.sum_comm]
    _ = sourceAAHProductLawExpectation := by
          unfold sourceAAHProductLawExpectation
          apply Finset.sum_congr rfl
          intro algorithm _
          apply Finset.sum_congr rfl
          intro order _
          apply Finset.sum_congr rfl
          intro human _
          rw [sourceAAHSequentialFocalCandidate_rankMean]

theorem sourceHAACardinalUtility_integral_eq_cast_direct :
    (∫ outcome, sourceHAACardinalUtility outcome ∂sourceHAACardinalProductLaw) =
      ((sourceDirectRankMeanExpectedHAA : ℚ) : ℝ) := by
  rw [sourceHAACardinalUtility_integral_eq_productLawExpectation,
    sourceHAAProductLawExpectation_eq_cast_direct]

theorem sourceAAHCardinalUtility_integral_eq_cast_direct :
    (∫ outcome, sourceAAHCardinalUtility outcome ∂sourceAAHCardinalProductLaw) =
      ((sourceDirectRankMeanExpectedAAH : ℚ) : ℝ) := by
  rw [sourceAAHCardinalUtility_integral_eq_productLawExpectation,
    sourceAAHProductLawExpectation_eq_cast_direct]

/-! ## Two-human mixed product experiments -/

/-- The sequential focal true-rank selector at the HAH profile. -/
def sourceHAHSequentialFocalCandidate
    (outcome : (SourceFourRanking × (SourceFourRanking × SourceFourRanking)) ×
      SourceFirmOrder) : SourceFourCandidate :=
  sourceFocalSelectedCandidate sourceProfileHAH outcome.1.1
    (sourceHumanRankings outcome.1.2.1 .r0123 outcome.1.2.2) outcome.2

/-- The sequential focal true-rank selector at the AHH profile. -/
def sourceAHHSequentialFocalCandidate
    (outcome : (SourceFourRanking × (SourceFourRanking × SourceFourRanking)) ×
      SourceFirmOrder) : SourceFourCandidate :=
  sourceFocalSelectedCandidate sourceProfileAHH outcome.1.1
    (sourceHumanRankings .r0123 outcome.1.2.1 outcome.1.2.2) outcome.2

theorem sourceHAHSequentialFocalCandidate_rankMean
    (algorithm h0 h2 : SourceFourRanking) (order : SourceFirmOrder) :
    sourceExpectedOrderStatisticValue
      (sourceHAHSequentialFocalCandidate ((algorithm, (h0, h2)), order)) =
      sourceFocalUtility sourceProfileHAH algorithm
        (sourceHumanRankings h0 .r0123 h2) order := by
  simpa [sourceHAHSequentialFocalCandidate] using
    (sourceFocalUtility_eq_selectedRankMean sourceProfileHAH algorithm
      (sourceHumanRankings h0 .r0123 h2) order).symm

theorem sourceAHHSequentialFocalCandidate_rankMean
    (algorithm h1 h2 : SourceFourRanking) (order : SourceFirmOrder) :
    sourceExpectedOrderStatisticValue
      (sourceAHHSequentialFocalCandidate ((algorithm, (h1, h2)), order)) =
      sourceFocalUtility sourceProfileAHH algorithm
        (sourceHumanRankings .r0123 h1 h2) order := by
  simpa [sourceAHHSequentialFocalCandidate] using
    (sourceFocalUtility_eq_selectedRankMean sourceProfileAHH algorithm
      (sourceHumanRankings .r0123 h1 h2) order).symm

noncomputable def sourceHAHCardinalProductLaw :
    Measure (((SourceFourRanking × (SourceFourRanking × SourceFourRanking)) ×
      SourceFirmOrder) × (Fin 4 → ℝ)) :=
  sourceTwoHumanProductLaw.toMeasure.prod sourceFourUniformValueLaw

noncomputable def sourceAHHCardinalProductLaw :
    Measure (((SourceFourRanking × (SourceFourRanking × SourceFourRanking)) ×
      SourceFirmOrder) × (Fin 4 → ℝ)) :=
  sourceTwoHumanProductLaw.toMeasure.prod sourceFourUniformValueLaw

noncomputable def sourceHAHCardinalUtility
    (outcome : ((SourceFourRanking × (SourceFourRanking × SourceFourRanking)) ×
      SourceFirmOrder) × (Fin 4 → ℝ)) : ℝ :=
  sourceFourSelectedUniformUtilityOf sourceHAHSequentialFocalCandidate outcome

noncomputable def sourceAHHCardinalUtility
    (outcome : ((SourceFourRanking × (SourceFourRanking × SourceFourRanking)) ×
      SourceFirmOrder) × (Fin 4 → ℝ)) : ℝ :=
  sourceFourSelectedUniformUtilityOf sourceAHHSequentialFocalCandidate outcome

theorem sourceHAHCardinalUtility_integral_eq_productLawExpectation :
    (∫ outcome, sourceHAHCardinalUtility outcome ∂sourceHAHCardinalProductLaw) =
      sourceHAHProductLawExpectation := by
  unfold sourceHAHCardinalUtility sourceHAHCardinalProductLaw
  rw [sourceFourSelectedUniformUtilityOf_integral_eq_weighted_table]
  calc
    (∑ outcome : (SourceFourRanking ×
      (SourceFourRanking × SourceFourRanking)) × SourceFirmOrder,
      (sourceTwoHumanProductLaw outcome).toReal *
        (sourceExpectedOrderStatisticValue
          (sourceHAHSequentialFocalCandidate outcome) : ℝ)) =
        ∑ algorithm : SourceFourRanking,
          ∑ h0 : SourceFourRanking,
            ∑ h2 : SourceFourRanking,
              ∑ order : SourceFirmOrder,
                (sourceTwoHumanProductLaw ((algorithm, (h0, h2)), order)).toReal *
                  (sourceExpectedOrderStatisticValue
                    (sourceHAHSequentialFocalCandidate ((algorithm, (h0, h2)), order)) : ℝ) := by
          rw [Fintype.sum_prod_type]
          simp_rw [Fintype.sum_prod_type]
    _ = ∑ algorithm : SourceFourRanking,
          ∑ order : SourceFirmOrder,
            ∑ h0 : SourceFourRanking,
              ∑ h2 : SourceFourRanking,
                (sourceTwoHumanProductLaw ((algorithm, (h0, h2)), order)).toReal *
                  (sourceExpectedOrderStatisticValue
                    (sourceHAHSequentialFocalCandidate ((algorithm, (h0, h2)), order)) : ℝ) := by
          apply Finset.sum_congr rfl
          intro algorithm _
          calc
            (∑ h0 : SourceFourRanking,
              ∑ h2 : SourceFourRanking,
                ∑ order : SourceFirmOrder,
                  (sourceTwoHumanProductLaw ((algorithm, (h0, h2)), order)).toReal *
                    (sourceExpectedOrderStatisticValue
                      (sourceHAHSequentialFocalCandidate ((algorithm, (h0, h2)), order)) : ℝ)) =
                ∑ h0 : SourceFourRanking,
                  ∑ order : SourceFirmOrder,
                    ∑ h2 : SourceFourRanking,
                      (sourceTwoHumanProductLaw ((algorithm, (h0, h2)), order)).toReal *
                        (sourceExpectedOrderStatisticValue
                          (sourceHAHSequentialFocalCandidate ((algorithm, (h0, h2)), order)) : ℝ) := by
                    apply Finset.sum_congr rfl
                    intro h0 _
                    exact Finset.sum_comm
            _ = ∑ order : SourceFirmOrder,
                  ∑ h0 : SourceFourRanking,
                    ∑ h2 : SourceFourRanking,
                      (sourceTwoHumanProductLaw ((algorithm, (h0, h2)), order)).toReal *
                        (sourceExpectedOrderStatisticValue
                          (sourceHAHSequentialFocalCandidate ((algorithm, (h0, h2)), order)) : ℝ) := by
                    exact Finset.sum_comm
    _ = sourceHAHProductLawExpectation := by
          unfold sourceHAHProductLawExpectation
          apply Finset.sum_congr rfl
          intro algorithm _
          apply Finset.sum_congr rfl
          intro order _
          apply Finset.sum_congr rfl
          intro h0 _
          apply Finset.sum_congr rfl
          intro h2 _
          rw [sourceHAHSequentialFocalCandidate_rankMean]

theorem sourceAHHCardinalUtility_integral_eq_productLawExpectation :
    (∫ outcome, sourceAHHCardinalUtility outcome ∂sourceAHHCardinalProductLaw) =
      sourceAHHProductLawExpectation := by
  unfold sourceAHHCardinalUtility sourceAHHCardinalProductLaw
  rw [sourceFourSelectedUniformUtilityOf_integral_eq_weighted_table]
  calc
    (∑ outcome : (SourceFourRanking ×
      (SourceFourRanking × SourceFourRanking)) × SourceFirmOrder,
      (sourceTwoHumanProductLaw outcome).toReal *
        (sourceExpectedOrderStatisticValue
          (sourceAHHSequentialFocalCandidate outcome) : ℝ)) =
        ∑ algorithm : SourceFourRanking,
          ∑ h1 : SourceFourRanking,
            ∑ h2 : SourceFourRanking,
              ∑ order : SourceFirmOrder,
                (sourceTwoHumanProductLaw ((algorithm, (h1, h2)), order)).toReal *
                  (sourceExpectedOrderStatisticValue
                    (sourceAHHSequentialFocalCandidate ((algorithm, (h1, h2)), order)) : ℝ) := by
          rw [Fintype.sum_prod_type]
          simp_rw [Fintype.sum_prod_type]
    _ = ∑ algorithm : SourceFourRanking,
          ∑ order : SourceFirmOrder,
            ∑ h1 : SourceFourRanking,
              ∑ h2 : SourceFourRanking,
                (sourceTwoHumanProductLaw ((algorithm, (h1, h2)), order)).toReal *
                  (sourceExpectedOrderStatisticValue
                    (sourceAHHSequentialFocalCandidate ((algorithm, (h1, h2)), order)) : ℝ) := by
          apply Finset.sum_congr rfl
          intro algorithm _
          calc
            (∑ h1 : SourceFourRanking,
              ∑ h2 : SourceFourRanking,
                ∑ order : SourceFirmOrder,
                  (sourceTwoHumanProductLaw ((algorithm, (h1, h2)), order)).toReal *
                    (sourceExpectedOrderStatisticValue
                      (sourceAHHSequentialFocalCandidate ((algorithm, (h1, h2)), order)) : ℝ)) =
                ∑ h1 : SourceFourRanking,
                  ∑ order : SourceFirmOrder,
                    ∑ h2 : SourceFourRanking,
                      (sourceTwoHumanProductLaw ((algorithm, (h1, h2)), order)).toReal *
                        (sourceExpectedOrderStatisticValue
                          (sourceAHHSequentialFocalCandidate ((algorithm, (h1, h2)), order)) : ℝ) := by
                    apply Finset.sum_congr rfl
                    intro h1 _
                    exact Finset.sum_comm
            _ = ∑ order : SourceFirmOrder,
                  ∑ h1 : SourceFourRanking,
                    ∑ h2 : SourceFourRanking,
                      (sourceTwoHumanProductLaw ((algorithm, (h1, h2)), order)).toReal *
                        (sourceExpectedOrderStatisticValue
                          (sourceAHHSequentialFocalCandidate ((algorithm, (h1, h2)), order)) : ℝ) := by
                    exact Finset.sum_comm
    _ = sourceAHHProductLawExpectation := by
          unfold sourceAHHProductLawExpectation
          apply Finset.sum_congr rfl
          intro algorithm _
          apply Finset.sum_congr rfl
          intro order _
          apply Finset.sum_congr rfl
          intro h1 _
          apply Finset.sum_congr rfl
          intro h2 _
          rw [sourceAHHSequentialFocalCandidate_rankMean]

theorem sourceHAHCardinalUtility_integral_eq_cast_direct :
    (∫ outcome, sourceHAHCardinalUtility outcome ∂sourceHAHCardinalProductLaw) =
      ((sourceDirectRankMeanExpectedHAH : ℚ) : ℝ) := by
  rw [sourceHAHCardinalUtility_integral_eq_productLawExpectation,
    sourceHAHProductLawExpectation_eq_cast_direct]

theorem sourceAHHCardinalUtility_integral_eq_cast_direct :
    (∫ outcome, sourceAHHCardinalUtility outcome ∂sourceAHHCardinalProductLaw) =
      ((sourceDirectRankMeanExpectedAHH : ℚ) : ℝ) := by
  rw [sourceAHHCardinalUtility_integral_eq_productLawExpectation,
    sourceAHHProductLawExpectation_eq_cast_direct]

/-! ## Independent all-human product experiment -/

/-- The sequential focal true-rank selector at the HHH profile. -/
def sourceHHHSequentialFocalCandidate
    (outcome : ((SourceFourRanking × SourceFourRanking) × SourceFourRanking) ×
      SourceFirmOrder) : SourceFourCandidate :=
  sourceFocalSelectedCandidate sourceProfileHHH .r0123
    (sourceHumanRankings outcome.1.1.1 outcome.1.1.2 outcome.1.2) outcome.2

theorem sourceHHHSequentialFocalCandidate_rankMean
    (h0 h1 h2 : SourceFourRanking) (order : SourceFirmOrder) :
    sourceExpectedOrderStatisticValue
      (sourceHHHSequentialFocalCandidate (((h0, h1), h2), order)) =
      sourceFocalUtility sourceProfileHHH .r0123
        (sourceHumanRankings h0 h1 h2) order := by
  simpa [sourceHHHSequentialFocalCandidate] using
    (sourceFocalUtility_eq_selectedRankMean sourceProfileHHH .r0123
      (sourceHumanRankings h0 h1 h2) order).symm

/-- The independent-three-human ranking/arrival law times the independent
iid-Uniform cardinal-value law. -/
noncomputable def sourceHHHCardinalProductLaw :
    Measure ((((SourceFourRanking × SourceFourRanking) × SourceFourRanking) ×
      SourceFirmOrder) × (Fin 4 → ℝ)) :=
  sourceHHHProductLaw.toMeasure.prod sourceFourUniformValueLaw

noncomputable def sourceHHHCardinalUtility
    (outcome : (((SourceFourRanking × SourceFourRanking) × SourceFourRanking) ×
      SourceFirmOrder) × (Fin 4 → ℝ)) : ℝ :=
  sourceFourSelectedUniformUtilityOf sourceHHHSequentialFocalCandidate outcome

theorem sourceHHHCardinalUtility_integral_eq_productLawExpectation :
    (∫ outcome, sourceHHHCardinalUtility outcome ∂sourceHHHCardinalProductLaw) =
      sourceHHHProductLawExpectation := by
  unfold sourceHHHCardinalUtility sourceHHHCardinalProductLaw
  rw [sourceFourSelectedUniformUtilityOf_integral_eq_weighted_table]
  calc
    (∑ outcome : ((SourceFourRanking × SourceFourRanking) × SourceFourRanking) ×
      SourceFirmOrder,
      (sourceHHHProductLaw outcome).toReal *
        (sourceExpectedOrderStatisticValue
          (sourceHHHSequentialFocalCandidate outcome) : ℝ)) =
        ∑ h0 : SourceFourRanking,
          ∑ h1 : SourceFourRanking,
            ∑ h2 : SourceFourRanking,
              ∑ order : SourceFirmOrder,
                (sourceHHHProductLaw (((h0, h1), h2), order)).toReal *
                  (sourceExpectedOrderStatisticValue
                    (sourceHHHSequentialFocalCandidate (((h0, h1), h2), order)) : ℝ) := by
          rw [Fintype.sum_prod_type]
          simp_rw [Fintype.sum_prod_type]
    _ = ∑ order : SourceFirmOrder,
          ∑ h0 : SourceFourRanking,
            ∑ h1 : SourceFourRanking,
              ∑ h2 : SourceFourRanking,
                (sourceHHHProductLaw (((h0, h1), h2), order)).toReal *
                  (sourceExpectedOrderStatisticValue
                    (sourceHHHSequentialFocalCandidate (((h0, h1), h2), order)) : ℝ) := by
          calc
            (∑ h0 : SourceFourRanking,
              ∑ h1 : SourceFourRanking,
                ∑ h2 : SourceFourRanking,
                  ∑ order : SourceFirmOrder,
                    (sourceHHHProductLaw (((h0, h1), h2), order)).toReal *
                      (sourceExpectedOrderStatisticValue
                        (sourceHHHSequentialFocalCandidate (((h0, h1), h2), order)) : ℝ)) =
                ∑ h0 : SourceFourRanking,
                  ∑ h1 : SourceFourRanking,
                    ∑ order : SourceFirmOrder,
                      ∑ h2 : SourceFourRanking,
                        (sourceHHHProductLaw (((h0, h1), h2), order)).toReal *
                          (sourceExpectedOrderStatisticValue
                            (sourceHHHSequentialFocalCandidate (((h0, h1), h2), order)) : ℝ) := by
                    apply Finset.sum_congr rfl
                    intro h0 _
                    apply Finset.sum_congr rfl
                    intro h1 _
                    exact Finset.sum_comm
            _ = ∑ h0 : SourceFourRanking,
                  ∑ order : SourceFirmOrder,
                    ∑ h1 : SourceFourRanking,
                      ∑ h2 : SourceFourRanking,
                        (sourceHHHProductLaw (((h0, h1), h2), order)).toReal *
                          (sourceExpectedOrderStatisticValue
                            (sourceHHHSequentialFocalCandidate (((h0, h1), h2), order)) : ℝ) := by
                    apply Finset.sum_congr rfl
                    intro h0 _
                    exact Finset.sum_comm
            _ = ∑ order : SourceFirmOrder,
                  ∑ h0 : SourceFourRanking,
                    ∑ h1 : SourceFourRanking,
                      ∑ h2 : SourceFourRanking,
                        (sourceHHHProductLaw (((h0, h1), h2), order)).toReal *
                          (sourceExpectedOrderStatisticValue
                            (sourceHHHSequentialFocalCandidate (((h0, h1), h2), order)) : ℝ) := by
                    exact Finset.sum_comm
    _ = sourceHHHProductLawExpectation := by
          unfold sourceHHHProductLawExpectation
          apply Finset.sum_congr rfl
          intro order _
          apply Finset.sum_congr rfl
          intro h0 _
          apply Finset.sum_congr rfl
          intro h1 _
          apply Finset.sum_congr rfl
          intro h2 _
          rw [sourceHHHSequentialFocalCandidate_rankMean]

theorem sourceHHHCardinalUtility_integral_eq_cast_direct :
    (∫ outcome, sourceHHHCardinalUtility outcome ∂sourceHHHCardinalProductLaw) =
      ((sourceDirectRankMeanExpectedHHH : ℚ) : ℝ) := by
  rw [sourceHHHCardinalUtility_integral_eq_productLawExpectation,
    sourceHHHProductLawExpectation_eq_cast_direct]

/-! ## Exact focal comparisons in the explicit cardinal product experiments -/

/-- For the labeled focal firm, using the shared algorithm beats using a human
when both opponents use the algorithm in the explicitly constructed cardinal
product experiments. -/
theorem sourceCardinalProduct_AAA_gt_HAA :
    (∫ outcome, sourceHAACardinalUtility outcome ∂sourceHAACardinalProductLaw) <
      ∫ outcome, sourceAAACardinalUtility outcome ∂sourceAAACardinalProductLaw := by
  rw [sourceHAACardinalUtility_integral_eq_cast_direct,
    sourceAAACardinalUtility_integral_eq_cast_direct,
    sourceDirectRankMeanExpectedHAA_eq, sourceDirectRankMeanExpectedAAA_eq]
  norm_num

/-- For the labeled focal firm, using the shared algorithm beats using a human
against one algorithmic and one human opponent in the explicit cardinal model. -/
theorem sourceCardinalProduct_AAH_gt_HAH :
    (∫ outcome, sourceHAHCardinalUtility outcome ∂sourceHAHCardinalProductLaw) <
      ∫ outcome, sourceAAHCardinalUtility outcome ∂sourceAAHCardinalProductLaw := by
  rw [sourceHAHCardinalUtility_integral_eq_cast_direct,
    sourceAAHCardinalUtility_integral_eq_cast_direct,
    sourceDirectRankMeanExpectedHAH_eq, sourceDirectRankMeanExpectedAAH_eq]
  norm_num

/-- For the labeled focal firm, using the shared algorithm beats using a human
when both opponents use humans in the explicit cardinal model. -/
theorem sourceCardinalProduct_AHH_gt_HHH :
    (∫ outcome, sourceHHHCardinalUtility outcome ∂sourceHHHCardinalProductLaw) <
      ∫ outcome, sourceAHHCardinalUtility outcome ∂sourceAHHCardinalProductLaw := by
  rw [sourceHHHCardinalUtility_integral_eq_cast_direct,
    sourceAHHCardinalUtility_integral_eq_cast_direct,
    sourceDirectRankMeanExpectedHHH_eq, sourceDirectRankMeanExpectedAHH_eq]
  norm_num

/-- The same explicit focal cardinal experiments exhibit the all-human versus
all-algorithm welfare ordering for the named focal firm.  Lifting this to a
social-welfare claim still requires the corresponding cardinal label-symmetry
bridge. -/
theorem sourceCardinalProduct_AAA_lt_HHH :
    (∫ outcome, sourceAAACardinalUtility outcome ∂sourceAAACardinalProductLaw) <
      ∫ outcome, sourceHHHCardinalUtility outcome ∂sourceHHHCardinalProductLaw := by
  rw [sourceAAACardinalUtility_integral_eq_cast_direct,
    sourceHHHCardinalUtility_integral_eq_cast_direct,
    sourceDirectRankMeanExpectedAAA_eq, sourceDirectRankMeanExpectedHHH_eq]
  norm_num

end KR21Monoculture
