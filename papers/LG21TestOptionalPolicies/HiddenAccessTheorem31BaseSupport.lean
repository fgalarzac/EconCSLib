import LG21TestOptionalPolicies.HiddenAccessTheorem31SourceTimedCandidateEntry

/-!
# Public-base support transport for LG21 Theorem 3.1

The source's positive-mass candidate semantics rule out a public-base set
which has positive population mass but no current reporters.  This module
records the resulting measure-theoretic support relation independently of a
strategy name or a particular candidate formula.  It is used to transport
on-path reporter-fibre facts to the literal source base population.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-- The base marginal of an action branch is the raw population restricted to
that branch and then observed through the public base. -/
theorem lg21_map_restrict_action_base_apply
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (law : Measure Omega) (base : Omega -> Base) (hbase : Measurable base)
    (actionEvent : Set Omega) (region : Set Base)
    (hregion : MeasurableSet region) :
    ((law.restrict actionEvent).map base) region =
      law (base ⁻¹' region ∩ actionEvent) := by
  rw [Measure.map_apply hbase hregion,
    Measure.restrict_apply (hregion.preimage hbase)]

/-- If every measurable positive public-base region would contain a positive
amount of an action branch, then the full base marginal is absolutely
continuous with respect to that branch's base marginal.  The hypothesis is
stated semantically in terms of sets and mass, so it is reusable for both
Theorem 3.1 regimes. -/
theorem lg21_baseMarginal_absolutelyContinuous_of_no_positive_branch_gap
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (law : Measure Omega) (base : Omega -> Base) (hbase : Measurable base)
    (actionEvent : Set Omega)
    (hnoGap : ∀ region : Set Base, MeasurableSet region ->
      0 < law (base ⁻¹' region) ->
      0 < law (base ⁻¹' region ∩ actionEvent)) :
    law.map base ≪ (law.restrict actionEvent).map base := by
  apply Measure.AbsolutelyContinuous.mk
  intro region hregion hbranchZero
  by_contra hbaseNonzero
  rw [Measure.map_apply hbase hregion] at hbaseNonzero
  have hbasePositive : 0 < law (base ⁻¹' region) :=
    pos_iff_ne_zero.mpr hbaseNonzero
  have hbranchPositive : 0 < law (base ⁻¹' region ∩ actionEvent) :=
    hnoGap region hregion hbasePositive
  have hbranchEq : law (base ⁻¹' region ∩ actionEvent) = 0 := by
    rw [← lg21_map_restrict_action_base_apply law base hbase actionEvent region hregion]
    exact hbranchZero
  exact (ne_of_gt hbranchPositive) hbranchEq

/-- The support conclusion is equivalently an almost-everywhere transport
principle.  This form is convenient when a reporter-fibre construction is
available only under its attained base law. -/
theorem lg21_ae_base_of_ae_branchBase_of_no_positive_branch_gap
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (law : Measure Omega) (base : Omega -> Base) (hbase : Measurable base)
    (actionEvent : Set Omega)
    (hnoGap : ∀ region : Set Base, MeasurableSet region ->
      0 < law (base ⁻¹' region) ->
      0 < law (base ⁻¹' region ∩ actionEvent))
    {p : Base -> Prop}
    (hp : ∀ᵐ publicBase ∂(law.restrict actionEvent).map base, p publicBase) :
    ∀ᵐ publicBase ∂law.map base, p publicBase := by
  exact (lg21_baseMarginal_absolutelyContinuous_of_no_positive_branch_gap
    law base hbase actionEvent hnoGap).ae_le hp

/-! ## Hidden-access source specialization -/

/-- Under literal source-local candidate stability, an entry construction for
every positive no-reporter base region makes the full public-base marginal
absolutely continuous with respect to the current reporter-base marginal.
This is the semantic bridge needed to use reporter-law a.e. facts at all
attained public bases. -/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.baseMarginal_absolutelyContinuous_reporterBase
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false})
    (hstable : LG21HiddenAccessSourceStableAgainstLocalCandidateEntry E hnoAccess)
    (hentry : ∀ region : Set (LG21NonTestFeature Feature testFeature -> ℝ),
      ∀ hregion : MeasurableSet region,
      ∀ hpositive : 0 < lg21ContinuousGaussianPopulationLaw M
        (lg21HiddenAccessBaseRegionEvent testFeature region),
      ∀ hzero : lg21ContinuousGaussianPopulationLaw M
        (lg21HiddenAccessBaseRegionEvent testFeature region ∩
          lg21HiddenAccessActualReportEvent E) = 0,
      LG21HiddenAccessSourceLocalCandidateEntry E hnoAccess) :
    (lg21ContinuousGaussianPopulationLaw M).map
        (fun student : Bool × (ℝ × (Feature -> ℝ)) =>
          lg21HiddenAccessStudentBase testFeature student.2) ≪
      ((lg21ContinuousGaussianPopulationLaw M).restrict
        (lg21HiddenAccessActualReportEvent E)).map
        (fun student : Bool × (ℝ × (Feature -> ℝ)) =>
          lg21HiddenAccessStudentBase testFeature student.2) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let base : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) :=
    fun student => lg21HiddenAccessStudentBase testFeature student.2
  let reporterEvent := lg21HiddenAccessActualReportEvent E
  have hbase : Measurable base := by
    simpa [base] using
      ((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd)
  apply lg21_baseMarginal_absolutelyContinuous_of_no_positive_branch_gap
    rawLaw base hbase reporterEvent
  intro region hregion hpositive
  by_contra hnotPositive
  have hzeroRaw : rawLaw (base ⁻¹' region ∩ reporterEvent) = 0 :=
    bot_unique (le_of_not_gt hnotPositive)
  have hregionEq : base ⁻¹' region =
      lg21HiddenAccessBaseRegionEvent testFeature region := by
    ext student
    rfl
  have hregionPositive : 0 < rawLaw
      (lg21HiddenAccessBaseRegionEvent testFeature region) := by
    simpa [hregionEq] using hpositive
  have hcurrentReporterZero : rawLaw
      (lg21HiddenAccessBaseRegionEvent testFeature region ∩
        lg21HiddenAccessActualReportEvent E) = 0 := by
    simpa [hregionEq, reporterEvent] using hzeroRaw
  exact hstable ⟨hentry region hregion hregionPositive hcurrentReporterZero⟩

/-- Literal stability against the source's local candidate entries implies
that the attained report branch itself has positive population mass.  This is
the `region = univ` instance of the same semantic condition used for the
base-support transport above. -/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.actualReportEvent_positive_of_stable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false})
    (hstable : LG21HiddenAccessSourceStableAgainstLocalCandidateEntry E hnoAccess)
    (hentry : ∀ region : Set (LG21NonTestFeature Feature testFeature -> ℝ),
      ∀ hregion : MeasurableSet region,
      ∀ hpositive : 0 < lg21ContinuousGaussianPopulationLaw M
        (lg21HiddenAccessBaseRegionEvent testFeature region),
      ∀ hzero : lg21ContinuousGaussianPopulationLaw M
        (lg21HiddenAccessBaseRegionEvent testFeature region ∩
          lg21HiddenAccessActualReportEvent E) = 0,
      LG21HiddenAccessSourceLocalCandidateEntry E hnoAccess) :
    0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessActualReportEvent E) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let region : Set (LG21NonTestFeature Feature testFeature -> ℝ) := Set.univ
  have hregionPositive : 0 < rawLaw
      (lg21HiddenAccessBaseRegionEvent testFeature region) := by
    change 0 < rawLaw Set.univ
    letI : IsProbabilityMeasure rawLaw := by
      simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
    simp
  by_contra hnotPositive
  have hreportZero : rawLaw (lg21HiddenAccessActualReportEvent E) = 0 :=
    bot_unique (le_of_not_gt hnotPositive)
  have hlocalZero : rawLaw
      (lg21HiddenAccessBaseRegionEvent testFeature region ∩
        lg21HiddenAccessActualReportEvent E) = 0 := by
    simpa [region, lg21HiddenAccessBaseRegionEvent] using hreportZero
  exact hstable ⟨hentry region MeasurableSet.univ hregionPositive hlocalZero⟩

/-- Independent access does not change the public non-test base marginal.
The equality is written for the literal pre-score access-decision law, so a
base-a.e. result can be lifted directly to the source's `Y` decision inputs. -/
theorem lg21HiddenAccessAccessLatentBaseLaw_map_base_eq_rawBaseLaw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature) :
    (lg21HiddenAccessAccessLatentBaseLaw M testFeature).map Prod.snd =
      (lg21ContinuousGaussianPopulationLaw M).map
        (fun student : Bool × (ℝ × (Feature -> ℝ)) =>
          lg21HiddenAccessStudentBase testFeature student.2) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let primitiveLaw := lg21ContinuousGaussianStudentPrimitiveLaw M
  let primitiveBase : ℝ × (Feature -> ℝ) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) :=
    lg21HiddenAccessStudentBase testFeature
  let latentBase : Bool × (ℝ × (Feature -> ℝ)) ->
      ℝ × (LG21NonTestFeature Feature testFeature -> ℝ) :=
    fun student => (lg21ContinuousPopulationSkill student,
      lg21HiddenAccessStudentBase testFeature student.2)
  have hprimitiveBase : Measurable primitiveBase := by
    simpa [primitiveBase] using
      (lg21HiddenAccessStudentBase_measurable testFeature)
  have hlatentBase : Measurable latentBase := by
    simpa [latentBase] using
      (lg21HiddenAccessLatentBaseObservation_measurable testFeature)
  letI : IsProbabilityMeasure primitiveLaw := by
    dsimp [primitiveLaw, lg21ContinuousGaussianStudentPrimitiveLaw,
      lg21ContinuousGaussianNoiseLaw]
    infer_instance
  have hrawStudent : rawLaw.map Prod.snd = primitiveLaw := by
    letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
    rw [show rawLaw = M.accessLaw.prod primitiveLaw by rfl,
      Measure.map_snd_prod, IsProbabilityMeasure.measure_univ, one_smul]
  have haccessStudent : accessLaw.map Prod.snd = primitiveLaw := by
    simpa [accessLaw, primitiveLaw] using
      (lg21ContinuousGaussianAccessPopulation_map_student_eq M haccess)
  calc
    (lg21HiddenAccessAccessLatentBaseLaw M testFeature).map Prod.snd =
        (accessLaw.map latentBase).map Prod.snd := by rfl
    _ = accessLaw.map (fun student =>
          lg21HiddenAccessStudentBase testFeature student.2) := by
      rw [Measure.map_map measurable_snd hlatentBase]
      rfl
    _ = (accessLaw.map Prod.snd).map primitiveBase := by
      rw [Measure.map_map hprimitiveBase measurable_snd]
      rfl
    _ = primitiveLaw.map primitiveBase := by rw [haccessStudent]
    _ = (rawLaw.map Prod.snd).map primitiveBase := by rw [hrawStudent]
    _ = rawLaw.map (fun student =>
          lg21HiddenAccessStudentBase testFeature student.2) := by
      rw [Measure.map_map hprimitiveBase measurable_snd]
      rfl

/-- Lift a public-base almost-everywhere property from the raw source
population to the literal positive-access pre-score decision law. -/
theorem lg21_ae_accessLatentBase_of_ae_rawBase
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    {p : (LG21NonTestFeature Feature testFeature -> ℝ) -> Prop}
    (hp : ∀ᵐ publicBase ∂(lg21ContinuousGaussianPopulationLaw M).map
      (fun student : Bool × (ℝ × (Feature -> ℝ)) =>
        lg21HiddenAccessStudentBase testFeature student.2), p publicBase) :
    ∀ᵐ profile ∂lg21HiddenAccessAccessLatentBaseLaw M testFeature,
      p profile.2 := by
  have hpAccessBase : ∀ᵐ publicBase ∂
      (lg21HiddenAccessAccessLatentBaseLaw M testFeature).map Prod.snd,
      p publicBase := by
    rw [lg21HiddenAccessAccessLatentBaseLaw_map_base_eq_rawBaseLaw
      M haccess testFeature]
    exact hp
  exact ae_of_ae_map measurable_snd.aemeasurable hpAccessBase

/-- A strict testing gain established at almost every raw public base rules
out literal positive-access no-takers.  The result keeps the source's
pre-score timing: the gain is evaluated under each student's actual test law
before Definition 1's a.e. taking best response is applied. -/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.activeNoTakeEvent_measure_zero_of_rawBaseStrictGain
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hbaseGain : ∀ᵐ publicBase ∂(lg21ContinuousGaussianPopulationLaw M).map
      (fun student : Bool × (ℝ × (Feature -> ℝ)) =>
        lg21HiddenAccessStudentBase testFeature student.2),
      ∀ latentSkill,
        E.noReportPayoff publicBase <
          ∫ score,
            if E.reportDecision publicBase score then
              E.reportedPayoff publicBase score
            else E.noReportPayoff publicBase
            ∂E.testLaw latentSkill publicBase) :
    lg21ContinuousGaussianPopulationLaw M E.activeNoTakeEvent = 0 := by
  apply E.activeNoTakeEvent_measure_zero_of_globalStrictGain
  have hprofileGain := lg21_ae_accessLatentBase_of_ae_rawBase
    M E.access_positive testFeature hbaseGain
  filter_upwards [hprofileGain] with profile hgain hnoTake
  exact hgain profile.1

/-- Combine the source-local no-zero-reporter-region principle with a strict
gain proved on the literal attained reporter-base law.  This is the final
measure step in the optional all-taking route: no case label or off-path PBO
is used. -/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.activeNoTakeEvent_measure_zero_of_reporterBaseStrictGain
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false})
    (hstable : LG21HiddenAccessSourceStableAgainstLocalCandidateEntry E hnoAccess)
    (hentry : ∀ region : Set (LG21NonTestFeature Feature testFeature -> ℝ),
      ∀ hregion : MeasurableSet region,
      ∀ hpositive : 0 < lg21ContinuousGaussianPopulationLaw M
        (lg21HiddenAccessBaseRegionEvent testFeature region),
      ∀ hzero : lg21ContinuousGaussianPopulationLaw M
        (lg21HiddenAccessBaseRegionEvent testFeature region ∩
          lg21HiddenAccessActualReportEvent E) = 0,
      LG21HiddenAccessSourceLocalCandidateEntry E hnoAccess)
    (hreporterGain : ∀ᵐ publicBase ∂
      ((lg21ContinuousGaussianPopulationLaw M).restrict
        (lg21HiddenAccessActualReportEvent E)).map
        (fun student : Bool × (ℝ × (Feature -> ℝ)) =>
          lg21HiddenAccessStudentBase testFeature student.2),
      ∀ latentSkill,
        E.noReportPayoff publicBase <
          ∫ score,
            if E.reportDecision publicBase score then
              E.reportedPayoff publicBase score
            else E.noReportPayoff publicBase
            ∂E.testLaw latentSkill publicBase) :
    lg21ContinuousGaussianPopulationLaw M E.activeNoTakeEvent = 0 := by
  apply E.activeNoTakeEvent_measure_zero_of_rawBaseStrictGain
  exact
    (E.baseMarginal_absolutelyContinuous_reporterBase hnoAccess hstable hentry).ae_le
      hreporterGain

end

end LG21TestOptionalPolicies
