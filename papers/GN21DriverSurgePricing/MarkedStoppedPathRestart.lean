import EconCSLib.Foundations.Probability.ExponentialInterarrivalUnboundedStopping
import EconCSLib.Foundations.Probability.PoissonFiniteHorizonMarkedThinning

/-!
# Finite marked stopped-path restart for GN21

This local module develops the finite-block restart theorem missing from the
GN21 source bridge on a literal IID stream of `(gap, acceptanceMark)` pairs.
It does not use a caller-supplied regeneration certificate.  The all-time
first-success limit and the CTMC restart remain separate obligations.
-/

namespace GN21DriverSurgePricing

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace IIDStream

variable {alpha : Type*} [MeasurableSpace alpha]

/-- The literal countable IID product law with one common coordinate law. -/
def measure (mu : Measure alpha) : Measure (Nat -> alpha) :=
  Measure.infinitePi (fun _ : Nat => mu)

/-- The `n`th coordinate of an IID stream. -/
def coordinate (n : Nat) : (Nat -> alpha) -> alpha := fun omega => omega n

theorem measurable_coordinate (n : Nat) : Measurable (coordinate (alpha := alpha) n) := by
  simpa [coordinate] using (measurable_pi_apply n : Measurable (fun omega : Nat -> alpha => omega n))

theorem coordinate_hasLaw (mu : Measure alpha) [IsProbabilityMeasure mu] (n : Nat) :
    HasLaw (coordinate (alpha := alpha) n) mu (measure mu) := by
  exact (@measurePreserving_eval_infinitePi Nat (fun _ : Nat => alpha)
    (fun _ => inferInstance) (fun _ : Nat => mu) (fun _ => inferInstance) n).hasLaw

theorem iIndepFun_coordinate (mu : Measure alpha) [IsProbabilityMeasure mu] :
    iIndepFun (coordinate (alpha := alpha)) (measure mu) := by
  simpa [measure, coordinate] using
    (@ProbabilityTheory.iIndepFun_infinitePi Nat (fun _ : Nat => alpha)
      (fun _ => inferInstance) (fun _ : Nat => alpha) (fun _ => inferInstance)
      (fun _ : Nat => mu) (fun _ => inferInstance)
      (fun _ => id) (fun _ => measurable_id))

/-- The inspected finite prefix through `n`. -/
def streamPrefix (n : Nat) : (Nat -> alpha) -> ((Finset.range (n + 1)) -> alpha) :=
  fun omega i => coordinate i omega

theorem measurable_streamPrefix (n : Nat) : Measurable (streamPrefix (alpha := alpha) n) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_coordinate i

/-- A deterministic finite block of consecutive IID coordinates. -/
def block (start q : Nat) : (Nat -> alpha) -> Fin q -> alpha :=
  fun omega i => coordinate (start + i) omega

theorem measurable_block (start q : Nat) : Measurable (block (alpha := alpha) start q) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_coordinate (start + i)

theorem iIndepFun_block (mu : Measure alpha) [IsProbabilityMeasure mu]
    (start q : Nat) :
    iIndepFun (fun (i : Fin q) omega => block (alpha := alpha) start q omega i)
      (measure mu) := by
  simpa [block] using
    (ProbabilityTheory.iIndepFun.precomp (g := fun i : Fin q => start + i)
      (by
        intro a b hab
        exact Fin.ext (Nat.add_left_cancel hab))
      (iIndepFun_coordinate mu))

/-- Pairing corresponding members of two finite independent families on a
product probability space preserves independence. -/
theorem iIndepFun_pair_prod
    {ι Ω₁ Ω₂ β γ : Type*}
    [Fintype ι]
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [MeasurableSpace β] [MeasurableSpace γ]
    {mu : Measure Ω₁} {nu : Measure Ω₂}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {X : ι -> Ω₁ -> β} {Y : ι -> Ω₂ -> γ}
    (hX : iIndepFun X mu) (hY : iIndepFun Y nu)
    (mX : forall i, Measurable (X i)) (mY : forall i, Measurable (Y i)) :
    iIndepFun (fun i z => (X i z.1, Y i z.2)) (mu.prod nu) := by
  classical
  let XV : Ω₁ -> (ι -> β) := fun omega i => X i omega
  let YV : Ω₂ -> (ι -> γ) := fun omega i => Y i omega
  have mXV : Measurable XV := measurable_pi_lambda _ mX
  have mYV : Measurable YV := measurable_pi_lambda _ mY
  have hmapX : mu.map XV = Measure.pi (fun i => mu.map (X i)) :=
    (iIndepFun_iff_map_fun_eq_pi_map
      (fun i => (mX i).aemeasurable)).mp hX
  have hmapY : nu.map YV = Measure.pi (fun i => nu.map (Y i)) :=
    (iIndepFun_iff_map_fun_eq_pi_map
      (fun i => (mY i).aemeasurable)).mp hY
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => ((mX i).comp measurable_fst).prodMk
      ((mY i).comp measurable_snd) |>.aemeasurable)).mpr
  let e := MeasurableEquiv.arrowProdEquivProdArrow β γ ι
  calc
    (mu.prod nu).map (fun z i => (X i z.1, Y i z.2)) =
        (mu.prod nu).map (e.symm ∘ Prod.map XV YV) := by
      congr 1
    _ = ((mu.prod nu).map (Prod.map XV YV)).map e.symm := by
      exact (Measure.map_map e.symm.measurable
        (mXV.comp measurable_fst |>.prodMk
          (mYV.comp measurable_snd))).symm
    _ = ((mu.map XV).prod (nu.map YV)).map e.symm := by
      rw [Measure.map_prod_map mu nu mXV mYV]
    _ = ((Measure.pi (fun i => mu.map (X i))).prod
          (Measure.pi (fun i => nu.map (Y i)))).map e.symm := by
      rw [hmapX, hmapY]
    _ = Measure.pi (fun i => (mu.map (X i)).prod (nu.map (Y i))) := by
      exact (measurePreserving_arrowProdEquivProdArrow β γ ι
        (fun i => mu.map (X i)) (fun i => nu.map (Y i))).symm.map_eq
    _ = Measure.pi (fun i =>
          (mu.prod nu).map (fun z => (X i z.1, Y i z.2))) := by
      congr 1
      funext i
      simpa [Prod.map] using Measure.map_prod_map mu nu (mX i) (mY i)

/-- Zip two streams into their coordinatewise pair stream. -/
def zip {beta : Type*} (omega : (Nat -> alpha) × (Nat -> beta)) : Nat -> alpha × beta :=
  fun n => (omega.1 n, omega.2 n)

theorem measurable_zip {beta : Type*} [MeasurableSpace beta] :
    Measurable (zip (alpha := alpha) (beta := beta)) := by
  apply measurable_pi_lambda
  intro n
  exact ((measurable_pi_apply n).comp measurable_fst).prodMk
    ((measurable_pi_apply n).comp measurable_snd)

/-- Two independent literal IID streams, zipped coordinatewise, form a
literal IID stream of paired coordinates. -/
theorem zip_hasLaw
    {beta : Type*} [MeasurableSpace beta]
    (mu : Measure alpha) (nu : Measure beta)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    HasLaw (zip (alpha := alpha) (beta := beta))
      (measure (mu.prod nu)) ((measure mu).prod (measure nu)) := by
  let source : Measure ((Nat -> alpha) × (Nat -> beta)) :=
    (measure mu).prod (measure nu)
  letI : IsProbabilityMeasure (measure mu) := by
    dsimp [measure]
    infer_instance
  letI : IsProbabilityMeasure (measure nu) := by
    dsimp [measure]
    infer_instance
  letI : IsProbabilityMeasure source := by
    dsimp [source, measure]
    infer_instance
  refine ⟨measurable_zip.aemeasurable, ?_⟩
  apply Measure.eq_infinitePi
  intro s t ht
  let pairVector : ((Nat -> alpha) × (Nat -> beta)) -> s -> alpha × beta :=
    fun omega i => (omega.1 i, omega.2 i)
  have hpairVector_meas : Measurable pairVector := by
    apply measurable_pi_lambda
    intro i
    exact ((measurable_pi_apply (i : Nat)).comp measurable_fst).prodMk
      ((measurable_pi_apply (i : Nat)).comp measurable_snd)
  have hX : iIndepFun (fun i : s => coordinate (alpha := alpha) i) (measure mu) :=
    (iIndepFun_coordinate mu).precomp (g := Subtype.val) Subtype.val_injective
  have hY : iIndepFun (fun i : s => coordinate (alpha := beta) i) (measure nu) :=
    (iIndepFun_coordinate nu).precomp (g := Subtype.val) Subtype.val_injective
  have hpair : iIndepFun
      (fun (i : s) (omega : (Nat -> alpha) × (Nat -> beta)) =>
        (coordinate (alpha := alpha) i omega.1,
          coordinate (alpha := beta) i omega.2)) source := by
    exact iIndepFun_pair_prod hX hY
      (fun i => measurable_coordinate (alpha := alpha) i)
      (fun i => measurable_coordinate (alpha := beta) i)
  have hpair_law : source.map pairVector =
      Measure.pi (fun _ : s => mu.prod nu) := by
    calc
      source.map pairVector = Measure.pi (fun i : s => source.map
          (fun omega : (Nat -> alpha) × (Nat -> beta) =>
            (coordinate (alpha := alpha) i omega.1,
              coordinate (alpha := beta) i omega.2))) := by
        simpa [source, pairVector] using
          (iIndepFun_iff_map_fun_eq_pi_map
            (fun (i : s) => ((measurable_coordinate (alpha := alpha) i).comp measurable_fst).prodMk
              ((measurable_coordinate (alpha := beta) i).comp measurable_snd) |>.aemeasurable)).mp
            hpair
      _ = Measure.pi (fun _ : s => mu.prod nu) := by
        congr 1
        funext i
        calc
          source.map
              (fun omega : (Nat -> alpha) × (Nat -> beta) =>
                (coordinate (alpha := alpha) i omega.1,
                  coordinate (alpha := beta) i omega.2)) =
              ((measure mu).map (coordinate (alpha := alpha) i)).prod
                ((measure nu).map (coordinate (alpha := beta) i)) := by
            symm
            simpa [source, IIDStream.coordinate, Prod.map] using
              Measure.map_prod_map (measure mu) (measure nu)
                (measurable_coordinate (alpha := alpha) i)
                (measurable_coordinate (alpha := beta) i)
          _ = mu.prod nu := by
            rw [(coordinate_hasLaw mu i).map_eq, (coordinate_hasLaw nu i).map_eq]
  have hpreimage :
      zip (alpha := alpha) (beta := beta) ⁻¹' Set.pi s t =
        pairVector ⁻¹' Set.univ.pi (fun i : s => t i) := by
    ext omega
    simp [zip, pairVector]
  calc
    source.map (zip (alpha := alpha) (beta := beta)) (Set.pi s t) =
        source (zip (alpha := alpha) (beta := beta) ⁻¹' Set.pi s t) :=
      Measure.map_apply measurable_zip
        (MeasurableSet.pi s.countable_toSet fun i _ => ht i)
    _ = source (pairVector ⁻¹' Set.univ.pi (fun i : s => t i)) := by
      rw [hpreimage]
    _ = source.map pairVector (Set.univ.pi (fun i : s => t i)) :=
      (Measure.map_apply hpairVector_meas (MeasurableSet.univ_pi fun i => ht i)).symm
    _ = Measure.pi (fun _ : s => mu.prod nu) (Set.univ.pi (fun i : s => t i)) := by
      rw [hpair_law]
    _ = ∏ i ∈ s, (mu.prod nu) (t i) := by
      rw [Measure.pi_pi]
      exact Finset.prod_coe_sort (s := s) (fun i => (mu.prod nu) (t i))

theorem block_hasLaw (mu : Measure alpha) [IsProbabilityMeasure mu]
    (start q : Nat) :
    HasLaw (block (alpha := alpha) start q) (Measure.pi (fun _ : Fin q => mu))
      (measure mu) := by
  letI : IsProbabilityMeasure (measure mu) := by
    dsimp [measure]
    infer_instance
  refine ⟨(measurable_block start q).aemeasurable, ?_⟩
  have hmap :=
    (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (f := fun (i : Fin q) omega => block (alpha := alpha) start q omega i)
      (μ := measure mu)
      (fun i => (measurable_coordinate (alpha := alpha) (start + i)).aemeasurable)).mp
      (iIndepFun_block mu start q)
  calc
    (measure mu).map (block (alpha := alpha) start q) =
        Measure.pi (fun i : Fin q =>
          (measure mu).map (fun omega => block (alpha := alpha) start q omega i)) := by
      simpa only using hmap
    _ = Measure.pi (fun _ : Fin q => mu) := by
      congr 1
      funext i
      exact (coordinate_hasLaw mu (start + i)).map_eq

/-- The inspected prefix through `n` is independent of every finite block after it. -/
theorem indepFun_streamPrefix_block (mu : Measure alpha) [IsProbabilityMeasure mu]
    (n q : Nat) :
    IndepFun (streamPrefix (alpha := alpha) n) (block (alpha := alpha) (n + 1) q)
      (measure mu) := by
  have hdisjoint : Disjoint (Finset.range (n + 1)) (Finset.Ico (n + 1) (n + 1 + q)) := by
    rw [Finset.disjoint_left]
    intro i hi hj
    have hil : i < n + 1 := Finset.mem_range.mp hi
    have hir : n + 1 <= i := (Finset.mem_Ico.mp hj).1
    omega
  have hraw := (iIndepFun_coordinate mu).indepFun_finset
    (Finset.range (n + 1)) (Finset.Ico (n + 1) (n + 1 + q)) hdisjoint
    (fun i => measurable_coordinate (alpha := alpha) i)
  let e : Fin q -> (Finset.Ico (n + 1) (n + 1 + q)) := fun i =>
    ⟨n + 1 + i, Finset.mem_Ico.mpr ⟨Nat.le_add_right _ _, by omega⟩⟩
  let reindex : ((Finset.Ico (n + 1) (n + 1 + q)) -> alpha) -> Fin q -> alpha :=
    fun g i => g (e i)
  have hreindex : Measurable reindex := by
    apply measurable_pi_lambda
    intro i
    exact measurable_pi_apply (e i)
  have hcomp := hraw.comp measurable_id hreindex
  simpa [streamPrefix, block, reindex, e, Function.comp_def] using hcomp

/-- Measurable rectangular events of a deterministic finite block factor coordinatewise. -/
theorem measure_block_mem_eq (mu : Measure alpha) [IsProbabilityMeasure mu]
    (start q : Nat) (s : Fin q -> Set alpha) (hs : forall i, MeasurableSet (s i)) :
    measure mu {omega | forall i, block (alpha := alpha) start q omega i ∈ s i} =
      ∏ i : Fin q, mu (s i) := by
  have hrect : {omega | forall i, block (alpha := alpha) start q omega i ∈ s i} =
      block (alpha := alpha) start q ⁻¹' Set.univ.pi s := by
    ext omega
    simp
  letI : forall i : Fin q, IsProbabilityMeasure mu := fun _ => inferInstance
  rw [hrect]
  calc
    measure mu (block (alpha := alpha) start q ⁻¹' Set.univ.pi s) =
        (measure mu).map (block (alpha := alpha) start q) (Set.univ.pi s) :=
      (Measure.map_apply (measurable_block start q) (MeasurableSet.univ_pi hs)).symm
    _ = Measure.pi (fun _ : Fin q => mu) (Set.univ.pi s) := by
      rw [(block_hasLaw mu start q).map_eq]
    _ = ∏ i : Fin q, mu (s i) := by
      rw [Measure.pi_pi]

/-- A total discrete stopping index whose level events inspect only the marked stream prefix. -/
structure PrefixStoppingIndex where
  toFun : (Nat -> alpha) -> Nat
  event_prefix_measurable : forall n,
    MeasurableSet[MeasurableSpace.comap (streamPrefix (alpha := alpha) n) inferInstance]
      {omega | toFun omega = n}

namespace PrefixStoppingIndex

instance : CoeFun (PrefixStoppingIndex (alpha := alpha))
    (fun _ => (Nat -> alpha) -> Nat) := ⟨PrefixStoppingIndex.toFun⟩

def event (tau : PrefixStoppingIndex (alpha := alpha)) (n : Nat) : Set (Nat -> alpha) :=
  {omega | tau omega = n}

theorem measurableSet_event (tau : PrefixStoppingIndex (alpha := alpha)) (n : Nat) :
    MeasurableSet (tau.event n) := by
  change MeasurableSet {omega | tau omega = n}
  rcases tau.event_prefix_measurable n with ⟨u, hu, hpre⟩
  rw [← hpre]
  exact (measurable_streamPrefix n) hu

theorem event_pairwiseDisjoint (tau : PrefixStoppingIndex (alpha := alpha)) :
    Pairwise (Function.onFun Disjoint tau.event) := by
  intro n m hnm
  refine Set.disjoint_left.2 ?_
  intro omega homega_n homega_m
  change tau omega = n at homega_n
  change tau omega = m at homega_m
  exact hnm (homega_n.symm.trans homega_m)

theorem iUnion_event_eq_univ (tau : PrefixStoppingIndex (alpha := alpha)) :
    ⋃ n, tau.event n = Set.univ := by
  ext omega
  simp [event]

/-- The first `q` uninspected marked coordinates after a total prefix stop. -/
def postBlock (tau : PrefixStoppingIndex (alpha := alpha)) (q : Nat) :
    (Nat -> alpha) -> Fin q -> alpha :=
  fun omega i => coordinate (tau omega + 1 + i) omega

private theorem measurable_postBlock_coordinate
    (tau : PrefixStoppingIndex (alpha := alpha)) (q : Nat) (i : Fin q) :
    Measurable (fun omega => postBlock tau q omega i) := by
  let h : forall omega : Nat -> alpha, exists n, tau omega = n := fun omega => ⟨tau omega, rfl⟩
  have hmeas : Measurable (fun omega => coordinate (Nat.find (h omega) + 1 + i) omega) :=
    Measurable.find
      (fun n => measurable_coordinate (alpha := alpha) (n + 1 + i))
      (fun n => tau.measurableSet_event n)
      h
  convert hmeas using 1
  funext omega
  have hfind : Nat.find (h omega) = tau omega := (Nat.find_spec (h omega)).symm
  simp [postBlock, hfind]

theorem measurable_postBlock (tau : PrefixStoppingIndex (alpha := alpha)) (q : Nat) :
    Measurable (postBlock tau q) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_postBlock_coordinate tau q i

/-- At a fixed stopping level, the uninspected marked block factors from the prefix. -/
theorem event_inter_block_measure_eq_mul
    (mu : Measure alpha) [IsProbabilityMeasure mu]
    (tau : PrefixStoppingIndex (alpha := alpha)) (n q : Nat)
    (s : Fin q -> Set alpha) (hs : forall i, MeasurableSet (s i)) :
    measure mu
      (tau.event n ∩ {omega | forall i, block (alpha := alpha) (n + 1) q omega i ∈ s i}) =
      measure mu (tau.event n) * ∏ i : Fin q, mu (s i) := by
  have hindep := indepFun_streamPrefix_block mu n q
  have hrect : {omega | forall i, block (alpha := alpha) (n + 1) q omega i ∈ s i} =
      block (alpha := alpha) (n + 1) q ⁻¹' Set.univ.pi s := by
    ext omega
    simp
  have hright : MeasurableSet[
      MeasurableSpace.comap (block (alpha := alpha) (n + 1) q) inferInstance]
      {omega | forall i, block (alpha := alpha) (n + 1) q omega i ∈ s i} := by
    rw [hrect]
    exact MeasurableSpace.measurableSet_comap.2
      ⟨Set.univ.pi s, MeasurableSet.univ_pi hs, rfl⟩
  have hfactor := hindep.meas_inter (tau.event_prefix_measurable n) hright
  calc
    measure mu
        (tau.event n ∩ {omega | forall i,
          block (alpha := alpha) (n + 1) q omega i ∈ s i}) =
        measure mu (tau.event n) *
          measure mu {omega | forall i,
            block (alpha := alpha) (n + 1) q omega i ∈ s i} := hfactor
    _ = measure mu (tau.event n) * ∏ i : Fin q, mu (s i) := by
      rw [measure_block_mem_eq mu (n + 1) q s hs]

/-- Every measurable rectangular event in a finite post-stop marked block has its IID law. -/
theorem measure_postBlock_mem_eq
    (mu : Measure alpha) [IsProbabilityMeasure mu]
    (tau : PrefixStoppingIndex (alpha := alpha)) (q : Nat)
    (s : Fin q -> Set alpha) (hs : forall i, MeasurableSet (s i)) :
    measure mu {omega | forall i, postBlock tau q omega i ∈ s i} =
      ∏ i : Fin q, mu (s i) := by
  let nu : Measure (Nat -> alpha) := measure mu
  letI : IsProbabilityMeasure nu := by
    dsimp [nu, measure]
    infer_instance
  let pieces : Nat -> Set (Nat -> alpha) := fun n =>
    tau.event n ∩ {omega | forall i, block (alpha := alpha) (n + 1) q omega i ∈ s i}
  have hblock_meas : forall n, MeasurableSet
      {omega | forall i, block (alpha := alpha) (n + 1) q omega i ∈ s i} := by
    intro n
    have hrect : {omega | forall i, block (alpha := alpha) (n + 1) q omega i ∈ s i} =
        block (alpha := alpha) (n + 1) q ⁻¹' Set.univ.pi s := by
      ext omega
      simp
    rw [hrect]
    exact (measurable_block (n + 1) q) (MeasurableSet.univ_pi hs)
  have hpieces_meas : forall n, MeasurableSet (pieces n) := by
    intro n
    exact (tau.measurableSet_event n).inter (hblock_meas n)
  have hpieces_disjoint : Pairwise (Function.onFun Disjoint pieces) := by
    intro n m hnm
    refine Set.disjoint_left.2 ?_
    intro omega homega_n homega_m
    have h_event_n : omega ∈ tau.event n := homega_n.1
    have h_event_m : omega ∈ tau.event m := homega_m.1
    change tau omega = n at h_event_n
    change tau omega = m at h_event_m
    exact hnm (h_event_n.symm.trans h_event_m)
  have hpieces_union :
      ⋃ n, pieces n = {omega | forall i, postBlock tau q omega i ∈ s i} := by
    ext omega
    simp only [Set.mem_iUnion, Set.mem_inter_iff, pieces, event, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, htau, hblock⟩
      simpa [postBlock, htau] using hblock
    · intro hmem
      refine ⟨tau omega, rfl, ?_⟩
      simpa [postBlock] using hmem
  have hmeasure_pieces :
      nu {omega | forall i, postBlock tau q omega i ∈ s i} =
        ∑' n, nu (pieces n) := by
    rw [← hpieces_union]
    exact measure_iUnion hpieces_disjoint hpieces_meas
  have hsum_event : ∑' n, nu (tau.event n) = 1 := by
    calc
      ∑' n, nu (tau.event n) = nu (⋃ n, tau.event n) :=
        (measure_iUnion tau.event_pairwiseDisjoint tau.measurableSet_event).symm
      _ = nu Set.univ := congrArg nu tau.iUnion_event_eq_univ
      _ = 1 := measure_univ
  have hpieces_factor :
      (∑' n, nu (pieces n)) =
        ∑' n, nu (tau.event n) * ∏ i : Fin q, mu (s i) := by
    apply tsum_congr
    intro n
    exact tau.event_inter_block_measure_eq_mul mu n q s hs
  change nu {omega | forall i, postBlock tau q omega i ∈ s i} = _
  calc
    nu {omega | forall i, postBlock tau q omega i ∈ s i} =
        ∑' n, nu (pieces n) := hmeasure_pieces
    _ = ∑' n, nu (tau.event n) * ∏ i : Fin q, mu (s i) := hpieces_factor
    _ = (∑' n, nu (tau.event n)) * ∏ i : Fin q, mu (s i) := by
      exact ENNReal.tsum_mul_right
    _ = ∏ i : Fin q, mu (s i) := by
      simp [hsum_event]

/-- The finite post-stop marked block has the original IID product law. -/
theorem postBlock_hasLaw
    (mu : Measure alpha) [IsProbabilityMeasure mu]
    (tau : PrefixStoppingIndex (alpha := alpha)) (q : Nat) :
    HasLaw (postBlock tau q) (Measure.pi (fun _ : Fin q => mu)) (measure mu) := by
  letI : IsProbabilityMeasure (measure mu) := by
    dsimp [measure]
    infer_instance
  refine ⟨(measurable_postBlock tau q).aemeasurable, ?_⟩
  apply (Measure.pi_eq (μ := fun _ : Fin q => mu)
    (μ' := (measure mu).map (postBlock tau q)) ?_).symm
  intro s hs
  have hrect : postBlock tau q ⁻¹' Set.univ.pi s =
      {omega | forall i, postBlock tau q omega i ∈ s i} := by
    ext omega
    simp
  calc
    (measure mu).map (postBlock tau q) (Set.univ.pi s) =
        measure mu (postBlock tau q ⁻¹' Set.univ.pi s) :=
      Measure.map_apply (measurable_postBlock tau q) (MeasurableSet.univ_pi hs)
    _ = measure mu {omega | forall i, postBlock tau q omega i ∈ s i} := congrArg _ hrect
    _ = ∏ i : Fin q, mu (s i) :=
      measure_postBlock_mem_eq mu tau q s hs

end PrefixStoppingIndex

end IIDStream

namespace MarkedRestart

/-- One literal IID GN21-style coordinate: an exponential gap and an acceptance bit. -/
abbrev Step := Real × Bool

/-- The acceptance bit at a raw arrival index. -/
def accepted (omega : Nat -> Step) (n : Nat) : Prop :=
  (omega n).2 = true

/-- The first accepted mark before `bound`, with `bound` as a total fallback.
When the true first success is at or after `bound`, this returns `bound`. -/
noncomputable def firstSuccessCapped (bound : Nat) (omega : Nat -> Step) : Nat := by
  classical
  exact if h : ∃ n, n < bound ∧ accepted omega n then Nat.find h else bound

theorem firstSuccessCapped_le (bound : Nat) (omega : Nat -> Step) :
    firstSuccessCapped bound omega <= bound := by
  classical
  unfold firstSuccessCapped
  split_ifs with h
  · exact (Nat.find_spec h).1.le
  · exact le_rfl

theorem firstSuccessCapped_eq_iff_of_lt
    {bound n : Nat} (hn : n < bound) (omega : Nat -> Step) :
    firstSuccessCapped bound omega = n ↔
      accepted omega n ∧ ∀ m < n, ¬ accepted omega m := by
  classical
  constructor
  · intro heq
    unfold firstSuccessCapped at heq
    by_cases hex : ∃ m, m < bound ∧ accepted omega m
    · have hspec : Nat.find hex < bound ∧ accepted omega (Nat.find hex) :=
        Nat.find_spec hex
      rw [dif_pos hex] at heq
      refine ⟨?_, ?_⟩
      · simpa [heq] using hspec.2
      · intro m hm haccepted
        have hlt : m < Nat.find hex := by simpa [heq] using hm
        exact (Nat.find_min hex hlt) ⟨lt_trans hm hn, haccepted⟩
    · rw [dif_neg hex] at heq
      exact False.elim ((ne_of_lt hn) heq.symm)
  · rintro ⟨haccepted, hprevious⟩
    let hex : ∃ m, m < bound ∧ accepted omega m := ⟨n, hn, haccepted⟩
    rw [firstSuccessCapped, dif_pos hex]
    apply Nat.le_antisymm
    · exact Nat.find_min' hex (m := n) ⟨hn, haccepted⟩
    · apply le_of_not_gt
      intro hlt
      exact hprevious (Nat.find hex) hlt (Nat.find_spec hex).2

theorem firstSuccessCapped_eq_bound_iff (bound : Nat) (omega : Nat -> Step) :
    firstSuccessCapped bound omega = bound ↔
      ∀ m < bound, ¬ accepted omega m := by
  classical
  constructor
  · intro heq
    unfold firstSuccessCapped at heq
    by_cases hex : ∃ m, m < bound ∧ accepted omega m
    · have hlt : Nat.find hex < bound := (Nat.find_spec hex).1
      rw [dif_pos hex] at heq
      exact False.elim ((ne_of_lt hlt) heq)
    · rw [dif_neg hex] at heq
      intro m hm haccepted
      exact hex ⟨m, hm, haccepted⟩
  · intro hprevious
    have hnone : ¬ ∃ m, m < bound ∧ accepted omega m := by
      rintro ⟨m, hm, haccepted⟩
      exact hprevious m hm haccepted
    simp [firstSuccessCapped, hnone]

private theorem measurable_prefix_accept_event (n : Nat) :
    MeasurableSet {x : (Finset.range (n + 1) -> Step) |
      (x ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n)⟩).2 = true} := by
  let iN : Finset.range (n + 1) :=
    ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n)⟩
  change MeasurableSet {x : (Finset.range (n + 1) -> Step) | (x iN).2 = true}
  exact (measurable_snd.comp (measurable_pi_apply iN)) (measurableSet_singleton true)

private theorem measurable_prefix_prior_reject_event (n : Nat) :
    MeasurableSet {x : (Finset.range (n + 1) -> Step) |
      ∀ m : Fin n,
        (x ⟨m, Finset.mem_range.mpr (Nat.lt_trans m.isLt (Nat.lt_succ_self n))⟩).2 ≠ true} := by
  let embed : Fin n -> Finset.range (n + 1) := fun m =>
    ⟨m, Finset.mem_range.mpr (Nat.lt_trans m.isLt (Nat.lt_succ_self n))⟩
  change MeasurableSet {x : (Finset.range (n + 1) -> Step) |
    ∀ m : Fin n, (x (embed m)).2 ≠ true}
  rw [show {x : (Finset.range (n + 1) -> Step) |
      ∀ m : Fin n, (x (embed m)).2 ≠ true} =
      ⋂ m : Fin n, {x | (x (embed m)).2 ≠ true} by
        ext x
        simp]
  apply MeasurableSet.iInter
  intro m
  exact ((measurable_snd.comp (measurable_pi_apply (embed m)))
    (measurableSet_singleton true)).compl

private theorem preimage_prefix_accept_event (n : Nat) :
    IIDStream.streamPrefix (alpha := Step) n ⁻¹'
      {x : (Finset.range (n + 1) -> Step) |
        (x ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n)⟩).2 = true} =
      {omega | accepted omega n} := by
  ext omega
  simp [IIDStream.streamPrefix, IIDStream.coordinate, accepted]

private theorem preimage_prefix_prior_reject_event (n : Nat) :
    IIDStream.streamPrefix (alpha := Step) n ⁻¹'
      {x : (Finset.range (n + 1) -> Step) |
        ∀ m : Fin n,
          (x ⟨m, Finset.mem_range.mpr (Nat.lt_trans m.isLt (Nat.lt_succ_self n))⟩).2 ≠ true} =
      {omega | ∀ m < n, ¬ accepted omega m} := by
  ext omega
  simp only [Set.mem_preimage, Set.mem_setOf_eq, IIDStream.streamPrefix,
    IIDStream.coordinate, accepted]
  constructor
  · intro h m hm
    exact h ⟨m, hm⟩
  · intro h m
    exact h m m.isLt

/-- The capped first success is a marked-prefix stopping index.  Its level event
at `n` reads only acceptance bits through arrival `n`. -/
def firstSuccessCappedStoppingIndex (bound : Nat) :
    IIDStream.PrefixStoppingIndex (alpha := Step) where
  toFun := firstSuccessCapped bound
  event_prefix_measurable := by
    intro n
    by_cases hlt : n < bound
    · let acceptEvent : Set (Finset.range (n + 1) -> Step) :=
        {x | (x ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n)⟩).2 = true}
      let priorRejectEvent : Set (Finset.range (n + 1) -> Step) :=
        {x | ∀ m : Fin n,
          (x ⟨m, Finset.mem_range.mpr (Nat.lt_trans m.isLt (Nat.lt_succ_self n))⟩).2 ≠ true}
      refine MeasurableSpace.measurableSet_comap.2
        ⟨acceptEvent ∩ priorRejectEvent, ?_, ?_⟩
      · exact (measurable_prefix_accept_event n).inter
          (measurable_prefix_prior_reject_event n)
      · rw [Set.preimage_inter, preimage_prefix_accept_event,
          preimage_prefix_prior_reject_event]
        ext omega
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
        exact (firstSuccessCapped_eq_iff_of_lt hlt omega).symm
    · by_cases heq : n = bound
      · subst n
        let priorRejectEvent : Set (Finset.range (bound + 1) -> Step) :=
          {x | ∀ m : Fin bound,
            (x ⟨m, Finset.mem_range.mpr
              (Nat.lt_trans m.isLt (Nat.lt_succ_self bound))⟩).2 ≠ true}
        refine MeasurableSpace.measurableSet_comap.2 ⟨priorRejectEvent, ?_, ?_⟩
        · exact measurable_prefix_prior_reject_event bound
        · rw [preimage_prefix_prior_reject_event]
          ext omega
          simp only [Set.mem_setOf_eq]
          exact (firstSuccessCapped_eq_bound_iff bound omega).symm
      · have hgt : bound < n := lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm heq)
        classical
        refine MeasurableSpace.measurableSet_comap.2 ⟨∅, MeasurableSet.empty, ?_⟩
        ext omega
        have hle := firstSuccessCapped_le bound omega
        have hne : firstSuccessCapped bound omega ≠ n := by omega
        simp [hne]

/-- One raw IID gap-and-mark coordinate law. -/
def stepLaw (rate : Real) (p : NNReal) (hp : p <= 1) : Measure Step :=
  (ProbabilityTheory.expMeasure rate).prod (PMF.bernoulli p hp).toMeasure

theorem isProbabilityMeasure_stepLaw
    {rate : Real} (hrate : 0 < rate) (p : NNReal) (hp : p <= 1) :
    IsProbabilityMeasure (stepLaw rate p hp) := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure rate) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
  dsimp [stepLaw]
  infer_instance

/-- The literal countable product measure of IID exponential gaps and IID acceptance bits. -/
def streamMeasure (rate : Real) (p : NNReal) (hp : p <= 1) : Measure (Nat -> Step) :=
  IIDStream.measure (stepLaw rate p hp)

/-- The event that one pair coordinate has a rejected Boolean mark. -/
def falseMarkSet : Set Step := Set.univ ×ˢ ({false} : Set Bool)

theorem stepLaw_falseMark
    {rate : Real} (hrate : 0 < rate) (p : NNReal) (hp : p <= 1) :
    stepLaw rate p hp falseMarkSet = ((1 - p : NNReal) : ENNReal) := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure rate) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
  rw [stepLaw, falseMarkSet, Measure.prod_prod]
  simp [PMF.bernoulli_apply]

theorem measurableSet_falseMarkSet : MeasurableSet falseMarkSet := by
  exact MeasurableSet.univ.prod (measurableSet_singleton false)

/-- The finite event that the first `count` acceptance bits are all false. -/
def noAcceptedPrefix (count : Nat) : Set (Nat -> Step) :=
  {omega | ∀ i : Fin count,
    IIDStream.block (alpha := Step) 0 count omega i ∈ falseMarkSet}

theorem measure_noAcceptedPrefix
    {rate : Real} (hrate : 0 < rate) (p : NNReal) (hp : p <= 1)
    (count : Nat) :
    streamMeasure rate p hp (noAcceptedPrefix count) =
      ((1 - p : NNReal) : ENNReal) ^ count := by
  letI : IsProbabilityMeasure (stepLaw rate p hp) :=
    isProbabilityMeasure_stepLaw hrate p hp
  unfold streamMeasure noAcceptedPrefix
  rw [IIDStream.measure_block_mem_eq (stepLaw rate p hp) 0 count
    (fun _ : Fin count => falseMarkSet)
    (fun _ => measurableSet_falseMarkSet)]
  simp [stepLaw_falseMark hrate p hp]

/-- The null-event complement of eventual acceptance. -/
def neverAccepted : Set (Nat -> Step) :=
  {omega | ∀ n, ¬ accepted omega n}

theorem neverAccepted_subset_noAcceptedPrefix (count : Nat) :
    neverAccepted ⊆ noAcceptedPrefix count := by
  intro omega homega i
  have hnot : (omega i).2 ≠ true := homega i
  simpa [IIDStream.block, IIDStream.coordinate, falseMarkSet] using hnot

theorem falseMarkProbability_lt_one
    (p : NNReal) (hpos : 0 < p) :
    ((1 - p : NNReal) : ENNReal) < 1 := by
  rw [← ENNReal.coe_one, ENNReal.coe_lt_coe]
  exact tsub_lt_self zero_lt_one hpos

/-- A positive iid Bernoulli acceptance probability makes a first accepted mark
exist almost surely on the literal gap-and-mark product path. -/
theorem ae_exists_accepted
    {rate : Real} (hrate : 0 < rate) (p : NNReal) (hp : p <= 1) (hpos : 0 < p) :
    ∀ᵐ omega ∂streamMeasure rate p hp, ∃ n, accepted omega n := by
  let mu := streamMeasure rate p hp
  let c : ENNReal := ((1 - p : NNReal) : ENNReal)
  have hsubset : ∀ count : Nat, neverAccepted ⊆ noAcceptedPrefix count :=
    neverAccepted_subset_noAcceptedPrefix
  have hbound : ∀ count : Nat, mu neverAccepted ≤ c ^ count := by
    intro count
    calc
      mu neverAccepted ≤ mu (noAcceptedPrefix count) := measure_mono (hsubset count)
      _ = c ^ count := by
        simpa [mu, c] using measure_noAcceptedPrefix hrate p hp count
  have hpow : Tendsto (fun count : Nat => c ^ count) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (by simpa [c] using falseMarkProbability_lt_one p hpos)
  have hzero : mu neverAccepted = 0 := by
    apply le_antisymm
    · exact le_of_tendsto_of_tendsto' tendsto_const_nhds hpow hbound
    · exact bot_le
  rw [MeasureTheory.ae_iff]
  simpa [mu, neverAccepted] using hzero

/-- The exact event that `n` is the first accepted arrival. -/
def firstSuccessEvent (n : Nat) : Set (Nat -> Step) :=
  {omega | accepted omega n ∧ ∀ m < n, ¬ accepted omega m}

theorem firstSuccessEvent_prefix_measurable (n : Nat) :
    MeasurableSet[MeasurableSpace.comap (IIDStream.streamPrefix (alpha := Step) n)
      inferInstance] (firstSuccessEvent n) := by
  have hcap := (firstSuccessCappedStoppingIndex (n + 1)).event_prefix_measurable n
  change MeasurableSet[MeasurableSpace.comap (IIDStream.streamPrefix (alpha := Step) n)
    inferInstance] {omega | firstSuccessCapped (n + 1) omega = n} at hcap
  convert hcap using 1
  ext omega
  simp only [Set.mem_setOf_eq, firstSuccessEvent]
  exact (firstSuccessCapped_eq_iff_of_lt (Nat.lt_succ_self n) omega).symm

theorem measurableSet_firstSuccessEvent (n : Nat) :
    MeasurableSet (firstSuccessEvent n) := by
  rcases firstSuccessEvent_prefix_measurable n with ⟨s, hs, hpre⟩
  rw [← hpre]
  exact (IIDStream.measurable_streamPrefix n) hs

theorem firstSuccessEvent_pairwiseDisjoint :
    Pairwise (Function.onFun Disjoint firstSuccessEvent) := by
  intro n m hne
  refine Set.disjoint_left.2 ?_
  intro omega hn hm
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (hm.2 n hlt) hn.1
  · exact (hn.2 m hgt) hm.1

theorem iUnion_firstSuccessEvent_eq_exists :
    ⋃ n, firstSuccessEvent n = {omega | ∃ n, accepted omega n} := by
  classical
  ext omega
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, hn.1⟩
  · rintro ⟨n, hn⟩
    let h : ∃ m, accepted omega m := ⟨n, hn⟩
    refine ⟨Nat.find h, (Nat.find_spec h), ?_⟩
    intro m hm haccepted
    exact (Nat.find_min h hm) haccepted

/-- The source's first accepted index, totalized only on the null no-success event. -/
noncomputable def firstSuccess (omega : Nat -> Step) : Nat := by
  classical
  exact if h : ∃ n, accepted omega n then Nat.find h else 0

theorem firstSuccess_eq_of_mem_firstSuccessEvent {n : Nat} {omega : Nat -> Step}
    (hmem : omega ∈ firstSuccessEvent n) :
    firstSuccess omega = n := by
  classical
  let hexists : ∃ m, accepted omega m := ⟨n, hmem.1⟩
  rw [firstSuccess, dif_pos hexists]
  apply Nat.le_antisymm
  · exact Nat.find_min' hexists (m := n) hmem.1
  · apply le_of_not_gt
    intro hlt
    exact hmem.2 (Nat.find hexists) hlt (Nat.find_spec hexists)

theorem firstSuccess_eq_zero_of_mem_neverAccepted {omega : Nat -> Step}
    (hmem : omega ∈ neverAccepted) :
    firstSuccess omega = 0 := by
  classical
  have hnone : ¬ ∃ n, accepted omega n := by
    rintro ⟨n, hn⟩
    exact hmem n hn
  simp [firstSuccess, hnone]

theorem firstSuccess_event_zero :
    {omega | firstSuccess omega = 0} = firstSuccessEvent 0 ∪ neverAccepted := by
  ext omega
  classical
  constructor
  · intro hzero
    change firstSuccess omega = 0 at hzero
    by_cases hexists : ∃ n, accepted omega n
    · left
      have hfind : Nat.find hexists = 0 := by
        rw [firstSuccess, dif_pos hexists] at hzero
        exact hzero
      refine ⟨?_, ?_⟩
      · have hspec := Nat.find_spec hexists
        rw [hfind] at hspec
        exact hspec
      · intro m hm haccepted
        omega
    · right
      intro n hn
      exact hexists ⟨n, hn⟩
  · rintro (hsuccess | hnever)
    · exact firstSuccess_eq_of_mem_firstSuccessEvent hsuccess
    · exact firstSuccess_eq_zero_of_mem_neverAccepted hnever

theorem firstSuccess_event_succ (n : Nat) :
    {omega | firstSuccess omega = n + 1} = firstSuccessEvent (n + 1) := by
  ext omega
  classical
  constructor
  · intro hsuccess
    change firstSuccess omega = n + 1 at hsuccess
    by_cases hexists : ∃ m, accepted omega m
    · have hfind : Nat.find hexists = n + 1 := by
        rw [firstSuccess, dif_pos hexists] at hsuccess
        exact hsuccess
      refine ⟨?_, ?_⟩
      · have hspec := Nat.find_spec hexists
        rw [hfind] at hspec
        exact hspec
      · intro m hm haccepted
        have hlt : m < Nat.find hexists := by
          rw [hfind]
          exact hm
        exact (Nat.find_min hexists hlt) haccepted
    · exfalso
      have hzero : firstSuccess omega = 0 := by simp [firstSuccess, hexists]
      omega
  · intro hsuccess
    exact firstSuccess_eq_of_mem_firstSuccessEvent hsuccess

theorem measurableSet_firstSuccess_event (n : Nat) :
    MeasurableSet {omega | firstSuccess omega = n} := by
  cases n with
  | zero =>
      rw [firstSuccess_event_zero]
      apply (measurableSet_firstSuccessEvent 0).union
      rw [show neverAccepted = ⋂ n, {omega | ¬ accepted omega n} by
        ext omega
        simp [neverAccepted]]
      apply MeasurableSet.iInter
      intro n
      exact ((measurable_snd.comp (measurable_pi_apply n))
        (measurableSet_singleton true)).compl
  | succ n =>
      rw [firstSuccess_event_succ]
      exact measurableSet_firstSuccessEvent (n + 1)

/-- The first `q` raw pair coordinates after the totalized first accepted arrival. -/
def postFirstSuccessBlock (q : Nat) : (Nat -> Step) -> Fin q -> Step :=
  fun omega i => IIDStream.coordinate (firstSuccess omega + 1 + i) omega

private theorem measurable_postFirstSuccessBlock_coordinate (q : Nat) (i : Fin q) :
    Measurable (fun omega => postFirstSuccessBlock q omega i) := by
  let h : ∀ omega : Nat -> Step, ∃ n, firstSuccess omega = n :=
    fun omega => ⟨firstSuccess omega, rfl⟩
  have hmeas : Measurable (fun omega =>
      IIDStream.coordinate (Nat.find (h omega) + 1 + i) omega) :=
    Measurable.find
      (fun n => IIDStream.measurable_coordinate (alpha := Step) (n + 1 + i))
      (fun n => measurableSet_firstSuccess_event n)
      h
  convert hmeas using 1
  funext omega
  have hfind : Nat.find (h omega) = firstSuccess omega := (Nat.find_spec (h omega)).symm
  simp [postFirstSuccessBlock, hfind]

theorem measurable_postFirstSuccessBlock (q : Nat) :
    Measurable (postFirstSuccessBlock q) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_postFirstSuccessBlock_coordinate q i

/-- At an exact first-success level, the later finite pair block factors from
the marked prefix.  This is the finite ingredient needed for the a.s.-finite
first-success restart theorem below. -/
theorem firstSuccessEvent_inter_block_measure_eq_mul
    (mu : Measure Step) [IsProbabilityMeasure mu]
    (n q : Nat) (s : Fin q -> Set Step) (hs : forall i, MeasurableSet (s i)) :
    IIDStream.measure mu
      (firstSuccessEvent n ∩
        {omega | forall i,
          IIDStream.block (alpha := Step) (n + 1) q omega i ∈ s i}) =
      IIDStream.measure mu (firstSuccessEvent n) * ∏ i : Fin q, mu (s i) := by
  let tau := firstSuccessCappedStoppingIndex (n + 1)
  have hevent : IIDStream.PrefixStoppingIndex.event tau n = firstSuccessEvent n := by
    ext omega
    change firstSuccessCapped (n + 1) omega = n ↔ _
    exact firstSuccessCapped_eq_iff_of_lt (Nat.lt_succ_self n) omega
  have h := IIDStream.PrefixStoppingIndex.event_inter_block_measure_eq_mul
    mu tau n q s hs
  rw [hevent] at h
  exact h

/-- Every measurable rectangular event in a finite block after the a.s.-finite
first accepted mark has its original IID probability. -/
theorem measure_postFirstSuccessBlock_mem_eq
    {rate : Real} (hrate : 0 < rate) (p : NNReal) (hp : p <= 1) (hpos : 0 < p)
    (q : Nat) (s : Fin q -> Set Step) (hs : forall i, MeasurableSet (s i)) :
    streamMeasure rate p hp
      {omega | forall i, postFirstSuccessBlock q omega i ∈ s i} =
      ∏ i : Fin q, stepLaw rate p hp (s i) := by
  let step : Measure Step := stepLaw rate p hp
  let mu : Measure (Nat -> Step) := IIDStream.measure step
  let good : Set (Nat -> Step) := ⋃ n, firstSuccessEvent n
  let postEvent : Set (Nat -> Step) :=
    {omega | forall i, postFirstSuccessBlock q omega i ∈ s i}
  let pieces : Nat -> Set (Nat -> Step) := fun n =>
    firstSuccessEvent n ∩
      {omega | forall i,
        IIDStream.block (alpha := Step) (n + 1) q omega i ∈ s i}
  letI : IsProbabilityMeasure step := by
    dsimp [step]
    exact isProbabilityMeasure_stepLaw hrate p hp
  letI : IsProbabilityMeasure mu := by
    dsimp [mu, IIDStream.measure]
    infer_instance
  have hgood_ae : ∀ᵐ omega ∂mu, omega ∈ good := by
    change ∀ᵐ omega ∂streamMeasure rate p hp, omega ∈ good
    filter_upwards [ae_exists_accepted hrate p hp hpos] with omega haccepted
    change omega ∈ ⋃ n, firstSuccessEvent n
    rw [iUnion_firstSuccessEvent_eq_exists]
    exact haccepted
  have hblock_meas : forall n, MeasurableSet
      {omega | forall i,
        IIDStream.block (alpha := Step) (n + 1) q omega i ∈ s i} := by
    intro n
    have hrect : {omega | forall i,
        IIDStream.block (alpha := Step) (n + 1) q omega i ∈ s i} =
        IIDStream.block (alpha := Step) (n + 1) q ⁻¹' Set.univ.pi s := by
      ext omega
      simp
    rw [hrect]
    exact (IIDStream.measurable_block (alpha := Step) (n + 1) q)
      (MeasurableSet.univ_pi hs)
  have hpieces_meas : forall n, MeasurableSet (pieces n) := by
    intro n
    exact (measurableSet_firstSuccessEvent n).inter (hblock_meas n)
  have hpieces_disjoint : Pairwise (Function.onFun Disjoint pieces) := by
    intro n m hnm
    refine Set.disjoint_left.2 ?_
    intro omega homega_n homega_m
    exact (Set.disjoint_left.1 (firstSuccessEvent_pairwiseDisjoint hnm))
      homega_n.1 homega_m.1
  have hpieces_union :
      ⋃ n, pieces n = postEvent ∩ good := by
    ext omega
    simp only [Set.mem_iUnion, Set.mem_inter_iff, pieces, postEvent, good,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hfirst, hblock⟩
      refine ⟨?_, ⟨n, hfirst⟩⟩
      have hindex := firstSuccess_eq_of_mem_firstSuccessEvent hfirst
      simpa [postFirstSuccessBlock, IIDStream.block, IIDStream.coordinate,
        hindex] using hblock
    · rintro ⟨hpost, ⟨n, hfirst⟩⟩
      refine ⟨n, hfirst, ?_⟩
      have hindex := firstSuccess_eq_of_mem_firstSuccessEvent hfirst
      simpa [postFirstSuccessBlock, IIDStream.block, IIDStream.coordinate,
        hindex] using hpost
  have hmeasure_pieces : mu postEvent = ∑' n, mu (pieces n) := by
    calc
      mu postEvent = mu (postEvent ∩ good) := by
        apply measure_congr
        filter_upwards [hgood_ae] with omega hmem
        apply propext
        constructor
        · intro hpost
          exact ⟨hpost, hmem⟩
        · exact fun hpost => hpost.1
      _ = mu (⋃ n, pieces n) := by rw [hpieces_union]
      _ = ∑' n, mu (pieces n) := measure_iUnion hpieces_disjoint hpieces_meas
  have hsum_event : ∑' n, mu (firstSuccessEvent n) = 1 := by
    calc
      ∑' n, mu (firstSuccessEvent n) = mu good := by
        dsimp [good]
        exact (measure_iUnion firstSuccessEvent_pairwiseDisjoint
          measurableSet_firstSuccessEvent).symm
      _ = mu Set.univ := by
        apply measure_congr
        filter_upwards [hgood_ae] with omega hmem
        apply propext
        constructor
        · intro _
          trivial
        · intro _
          exact hmem
      _ = 1 := measure_univ
  have hpieces_factor :
      (∑' n, mu (pieces n)) =
        ∑' n, mu (firstSuccessEvent n) * ∏ i : Fin q, step (s i) := by
    apply tsum_congr
    intro n
    change IIDStream.measure step
      (firstSuccessEvent n ∩
        {omega | forall i,
          IIDStream.block (alpha := Step) (n + 1) q omega i ∈ s i}) =
      IIDStream.measure step (firstSuccessEvent n) * ∏ i : Fin q, step (s i)
    exact firstSuccessEvent_inter_block_measure_eq_mul step n q s hs
  change mu postEvent = _
  calc
    mu postEvent = ∑' n, mu (pieces n) := hmeasure_pieces
    _ = ∑' n, mu (firstSuccessEvent n) * ∏ i : Fin q, step (s i) :=
      hpieces_factor
    _ = (∑' n, mu (firstSuccessEvent n)) * ∏ i : Fin q, step (s i) := by
      exact ENNReal.tsum_mul_right
    _ = ∏ i : Fin q, step (s i) := by simp [hsum_event]

/-- A positive IID acceptance probability makes the post-first-success finite
pair block IID again.  The theorem is about the literal pair stream, so it
retains the dependence between each exponential gap and its paired mark. -/
theorem postFirstSuccessBlock_hasLaw
    {rate : Real} (hrate : 0 < rate) (p : NNReal) (hp : p <= 1) (hpos : 0 < p)
    (q : Nat) :
    HasLaw (postFirstSuccessBlock q)
      (Measure.pi (fun _ : Fin q => stepLaw rate p hp))
      (streamMeasure rate p hp) := by
  letI : IsProbabilityMeasure (stepLaw rate p hp) :=
    isProbabilityMeasure_stepLaw hrate p hp
  letI : IsProbabilityMeasure (streamMeasure rate p hp) := by
    dsimp [streamMeasure, IIDStream.measure]
    infer_instance
  refine ⟨(measurable_postFirstSuccessBlock q).aemeasurable, ?_⟩
  apply (Measure.pi_eq (μ := fun _ : Fin q => stepLaw rate p hp)
    (μ' := (streamMeasure rate p hp).map (postFirstSuccessBlock q)) ?_).symm
  intro s hs
  have hrect : postFirstSuccessBlock q ⁻¹' Set.univ.pi s =
      {omega | forall i, postFirstSuccessBlock q omega i ∈ s i} := by
    ext omega
    simp
  calc
    (streamMeasure rate p hp).map (postFirstSuccessBlock q) (Set.univ.pi s) =
        streamMeasure rate p hp (postFirstSuccessBlock q ⁻¹' Set.univ.pi s) :=
      Measure.map_apply (measurable_postFirstSuccessBlock q)
        (MeasurableSet.univ_pi hs)
    _ = streamMeasure rate p hp
        {omega | forall i, postFirstSuccessBlock q omega i ∈ s i} :=
      congrArg _ hrect
    _ = ∏ i : Fin q, stepLaw rate p hp (s i) :=
      measure_postFirstSuccessBlock_mem_eq hrate p hp hpos q s hs

/-- Direct finite marked restart at the capped first accepted arrival.  The entire
post-stop pair block, not merely its gap or mark projection, has the original IID law. -/
theorem firstSuccessCapped_postBlock_hasLaw
    {rate : Real} (hrate : 0 < rate) (p : NNReal) (hp : p <= 1)
    (bound q : Nat) :
    HasLaw
      (IIDStream.PrefixStoppingIndex.postBlock (firstSuccessCappedStoppingIndex bound) q)
      (Measure.pi (fun _ : Fin q => stepLaw rate p hp))
      (streamMeasure rate p hp) := by
  letI : IsProbabilityMeasure (stepLaw rate p hp) :=
    isProbabilityMeasure_stepLaw hrate p hp
  simpa [streamMeasure] using
    (IIDStream.PrefixStoppingIndex.postBlock_hasLaw (stepLaw rate p hp)
      (firstSuccessCappedStoppingIndex bound) q)

end MarkedRestart

end

end GN21DriverSurgePricing
