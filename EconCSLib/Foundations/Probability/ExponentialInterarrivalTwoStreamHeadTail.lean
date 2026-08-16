import EconCSLib.Foundations.Probability.ExponentialInterarrivalFiniteHeadTail
import Mathlib.Tactic

/-!
# Literal two-stream head-tail factors

This module factors two independent one-sided exponential paths together with
an independent initial state.  It exposes the nearest coordinate of each
path and the complete strictly older tails.  The order of every coordinate is
recorded explicitly, so recurrence arguments cannot silently replace a
shifted source path with a fresh independent input.

No queueing or stationary-law conclusion is made here.
-/

namespace EconCSLib.Probability.PoissonProcess

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Split two literal one-sided paths at their nearest coordinates while
retaining an arbitrary independent initial state with the strictly older
tails. -/
def initialTwoStreamHeadTailFactors {Ω : Type*}
    (x : Ω × ((Nat → Real) × (Nat → Real))) :
    (Ω × ((Nat → Real) × (Nat → Real))) × (Real × Real) :=
  ((x.1, (fun n => x.2.1 (n + 1), fun n => x.2.2 (n + 1))),
    (x.2.1 0, x.2.2 0))

/-- The two-stream literal factorization is measurable. -/
theorem measurable_initialTwoStreamHeadTailFactors {Ω : Type*}
    [MeasurableSpace Ω] :
    Measurable (initialTwoStreamHeadTailFactors (Ω := Ω)) := by
  unfold initialTwoStreamHeadTailFactors
  exact
    ((measurable_fst.prodMk
      ((measurable_pi_iff.2 fun n =>
        measurable_pi_apply (n + 1) |>.comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_pi_iff.2 fun n =>
          measurable_pi_apply (n + 1) |>.comp (measurable_snd.comp measurable_snd)))).prodMk
      (((measurable_pi_apply 0).comp (measurable_fst.comp measurable_snd)).prodMk
        ((measurable_pi_apply 0).comp (measurable_snd.comp measurable_snd))))

/-- The raw product reordering after independently splitting both one-sided
paths. -/
private def initialTwoStreamHeadTailRearrange {Ω : Type*}
    (x : Ω × ((Real × (Nat → Real)) × (Real × (Nat → Real)))) :
    (Ω × ((Nat → Real) × (Nat → Real))) × (Real × Real) :=
  ((x.1, (x.2.1.2, x.2.2.2)), (x.2.1.1, x.2.2.1))

private theorem measurable_initialTwoStreamHeadTailRearrange {Ω : Type*}
    [MeasurableSpace Ω] :
    Measurable (initialTwoStreamHeadTailRearrange (Ω := Ω)) := by
  unfold initialTwoStreamHeadTailRearrange
  exact
    ((measurable_fst.prodMk
      ((measurable_snd.comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))).prodMk
      ((measurable_fst.comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd))))

private theorem initialTwoStreamHeadTailFactors_eq_rearrange {Ω : Type*}
    (x : Ω × ((Nat → Real) × (Nat → Real))) :
    initialTwoStreamHeadTailFactors x =
      initialTwoStreamHeadTailRearrange
        (Prod.map id (Prod.map headTail headTail) x) := by
  rfl

private def prodRotateMiddleRight {α β γ : Type*}
    (x : α × (β × γ)) : (α × γ) × β :=
  ((x.1, x.2.2), x.2.1)

private theorem measurable_prodRotateMiddleRight {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] :
    Measurable (prodRotateMiddleRight (α := α) (β := β) (γ := γ)) := by
  unfold prodRotateMiddleRight
  exact ((measurable_fst.prodMk (measurable_snd.comp measurable_snd)).prodMk
    (measurable_fst.comp measurable_snd))

private theorem map_prodRotateMiddleRight
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) (ξ : Measure γ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ] :
    Measure.map (prodRotateMiddleRight (α := α) (β := β) (γ := γ))
      (μ.prod (ν.prod ξ)) = (μ.prod ξ).prod ν := by
  have hassocSymm :
      Measure.map (MeasurableEquiv.prodAssoc.symm : α × (β × γ) → (α × β) × γ)
        (μ.prod (ν.prod ξ)) = (μ.prod ν).prod ξ := by
    rw [← Measure.prodAssoc_prod]
    rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
      MeasurableEquiv.prodAssoc.measurable]
    have hcomp :
        (MeasurableEquiv.prodAssoc.symm : α × (β × γ) → (α × β) × γ) ∘
          (MeasurableEquiv.prodAssoc : (α × β) × γ → α × (β × γ)) = id := by
      funext x
      rfl
    rw [hcomp, Measure.map_id]
  calc
    Measure.map (prodRotateMiddleRight (α := α) (β := β) (γ := γ))
        (μ.prod (ν.prod ξ)) =
      Measure.map Prod.swap
        (Measure.map (MeasurableEquiv.prodAssoc : (β × α) × γ → β × (α × γ))
          (Measure.map (Prod.map Prod.swap id)
            (Measure.map (MeasurableEquiv.prodAssoc.symm : α × (β × γ) → (α × β) × γ)
              (μ.prod (ν.prod ξ))))) := by
        symm
        rw [Measure.map_map (measurable_swap.prodMap measurable_id)
            MeasurableEquiv.prodAssoc.symm.measurable,
          Measure.map_map MeasurableEquiv.prodAssoc.measurable
            ((measurable_swap.prodMap measurable_id).comp
              MeasurableEquiv.prodAssoc.symm.measurable),
          Measure.map_map measurable_swap
            (MeasurableEquiv.prodAssoc.measurable.comp
              ((measurable_swap.prodMap measurable_id).comp
                MeasurableEquiv.prodAssoc.symm.measurable))]
        rfl
    _ = Measure.map Prod.swap
        (Measure.map (MeasurableEquiv.prodAssoc : (β × α) × γ → β × (α × γ))
          (Measure.map (Prod.map Prod.swap id) ((μ.prod ν).prod ξ))) := by
        rw [hassocSymm]
    _ = Measure.map Prod.swap
        (Measure.map (MeasurableEquiv.prodAssoc : (β × α) × γ → β × (α × γ))
          ((ν.prod μ).prod ξ)) := by
        rw [← Measure.map_prod_map _ _ measurable_swap measurable_id,
          Measure.prod_swap, Measure.map_id]
    _ = Measure.map Prod.swap (ν.prod (μ.prod ξ)) := by
        rw [Measure.prodAssoc_prod]
    _ = (μ.prod ξ).prod ν := by
        rw [Measure.prod_swap]

private def prodRotateMiddleLeft {α β γ : Type*}
    (x : α × (β × γ)) : β × (α × γ) :=
  (x.2.1, (x.1, x.2.2))

private theorem measurable_prodRotateMiddleLeft {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] :
    Measurable (prodRotateMiddleLeft (α := α) (β := β) (γ := γ)) := by
  unfold prodRotateMiddleLeft
  exact (measurable_fst.comp measurable_snd).prodMk
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd))

private theorem map_prodRotateMiddleLeft
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) (ξ : Measure γ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ] :
    Measure.map (prodRotateMiddleLeft (α := α) (β := β) (γ := γ))
      (μ.prod (ν.prod ξ)) = ν.prod (μ.prod ξ) := by
  calc
    Measure.map (prodRotateMiddleLeft (α := α) (β := β) (γ := γ))
        (μ.prod (ν.prod ξ)) =
      Measure.map Prod.swap
        (Measure.map (prodRotateMiddleRight (α := α) (β := β) (γ := γ))
          (μ.prod (ν.prod ξ))) := by
        symm
        rw [Measure.map_map measurable_swap measurable_prodRotateMiddleRight]
        rfl
    _ = Measure.map Prod.swap ((μ.prod ξ).prod ν) := by
        rw [map_prodRotateMiddleRight]
    _ = ν.prod (μ.prod ξ) := by
        rw [Measure.prod_swap]

private def prodMiddleSwap {α β γ δ : Type*}
    (x : (α × β) × (γ × δ)) : (α × γ) × (β × δ) :=
  ((x.1.1, x.2.1), (x.1.2, x.2.2))

private theorem measurable_prodMiddleSwap {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ] :
    Measurable (prodMiddleSwap (α := α) (β := β) (γ := γ) (δ := δ)) := by
  unfold prodMiddleSwap
  exact
    ((measurable_fst.comp measurable_fst).prodMk
      (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_snd.comp measurable_fst).prodMk
        (measurable_snd.comp measurable_snd))

private theorem map_prodMiddleSwap
    {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (μ : Measure α) (ν : Measure β) (ξ : Measure γ) (ζ : Measure δ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ξ] [IsProbabilityMeasure ζ] :
    Measure.map (prodMiddleSwap (α := α) (β := β) (γ := γ) (δ := δ))
      ((μ.prod ν).prod (ξ.prod ζ)) = (μ.prod ξ).prod (ν.prod ζ) := by
  have hleft :
      Measure.map (MeasurableEquiv.prodAssoc : (α × β) × (γ × δ) →
        α × (β × (γ × δ))) ((μ.prod ν).prod (ξ.prod ζ)) =
        μ.prod (ν.prod (ξ.prod ζ)) := by
    exact Measure.prodAssoc_prod
  have hmiddle :
      Measure.map (Prod.map id (prodRotateMiddleLeft (α := β) (β := γ) (γ := δ)))
        (μ.prod (ν.prod (ξ.prod ζ))) = μ.prod (ξ.prod (ν.prod ζ)) := by
    rw [← Measure.map_prod_map _ _ measurable_id measurable_prodRotateMiddleLeft,
      Measure.map_id, map_prodRotateMiddleLeft]
  have hright :
      Measure.map (MeasurableEquiv.prodAssoc.symm : α × (γ × (β × δ)) →
        (α × γ) × (β × δ)) (μ.prod (ξ.prod (ν.prod ζ))) =
        (μ.prod ξ).prod (ν.prod ζ) := by
    rw [← Measure.prodAssoc_prod]
    rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
      MeasurableEquiv.prodAssoc.measurable]
    have hcomp :
        (MeasurableEquiv.prodAssoc.symm : α × (γ × (β × δ)) →
          (α × γ) × (β × δ)) ∘
          (MeasurableEquiv.prodAssoc : (α × γ) × (β × δ) →
            α × (γ × (β × δ))) = id := by
      funext x
      rfl
    rw [hcomp, Measure.map_id]
  calc
    Measure.map (prodMiddleSwap (α := α) (β := β) (γ := γ) (δ := δ))
        ((μ.prod ν).prod (ξ.prod ζ)) =
      Measure.map (MeasurableEquiv.prodAssoc.symm : α × (γ × (β × δ)) →
        (α × γ) × (β × δ))
        (Measure.map (Prod.map id (prodRotateMiddleLeft (α := β) (β := γ) (γ := δ)))
          (Measure.map (MeasurableEquiv.prodAssoc : (α × β) × (γ × δ) →
            α × (β × (γ × δ))) ((μ.prod ν).prod (ξ.prod ζ)))) := by
        symm
        rw [Measure.map_map (measurable_id.prodMap measurable_prodRotateMiddleLeft)
          MeasurableEquiv.prodAssoc.measurable,
          Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
            ((measurable_id.prodMap measurable_prodRotateMiddleLeft).comp
              MeasurableEquiv.prodAssoc.measurable)]
        rfl
    _ = Measure.map (MeasurableEquiv.prodAssoc.symm : α × (γ × (β × δ)) →
        (α × γ) × (β × δ))
        (Measure.map (Prod.map id (prodRotateMiddleLeft (α := β) (β := γ) (γ := δ)))
          (μ.prod (ν.prod (ξ.prod ζ)))) := by rw [hleft]
    _ = Measure.map (MeasurableEquiv.prodAssoc.symm : α × (γ × (β × δ)) →
        (α × γ) × (β × δ)) (μ.prod (ξ.prod (ν.prod ζ))) := by rw [hmiddle]
    _ = (μ.prod ξ).prod (ν.prod ζ) := hright

private theorem map_initialTwoStreamHeadTailRearrange
    {Ω : Type*} [MeasurableSpace Ω]
    (initialLaw : Measure Ω) [IsProbabilityMeasure initialLaw]
    {leftRate rightRate : Real} (hleft : 0 < leftRate) (hright : 0 < rightRate) :
    Measure.map (initialTwoStreamHeadTailRearrange (Ω := Ω))
      (initialLaw.prod
        (((expMeasure leftRate).prod (exponentialInterarrivalMeasure leftRate)).prod
          ((expMeasure rightRate).prod (exponentialInterarrivalMeasure rightRate)))) =
      (initialLaw.prod
        ((exponentialInterarrivalMeasure leftRate).prod
          (exponentialInterarrivalMeasure rightRate))).prod
        ((expMeasure leftRate).prod (expMeasure rightRate)) := by
  letI : IsProbabilityMeasure (expMeasure leftRate) :=
    isProbabilityMeasure_expMeasure hleft
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure leftRate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hleft
  letI : IsProbabilityMeasure (expMeasure rightRate) :=
    isProbabilityMeasure_expMeasure hright
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rightRate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hright
  have houter :
      Measure.map
        (MeasurableEquiv.prodAssoc.symm :
          Ω × ((Real × (Nat → Real)) × (Real × (Nat → Real))) →
            (Ω × (Real × (Nat → Real))) × (Real × (Nat → Real)))
        (initialLaw.prod
          (((expMeasure leftRate).prod (exponentialInterarrivalMeasure leftRate)).prod
            ((expMeasure rightRate).prod (exponentialInterarrivalMeasure rightRate)))) =
        (initialLaw.prod ((expMeasure leftRate).prod
          (exponentialInterarrivalMeasure leftRate))).prod
          ((expMeasure rightRate).prod (exponentialInterarrivalMeasure rightRate)) := by
    rw [← Measure.prodAssoc_prod]
    rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
      MeasurableEquiv.prodAssoc.measurable]
    have hcomp :
        (MeasurableEquiv.prodAssoc.symm :
          Ω × ((Real × (Nat → Real)) × (Real × (Nat → Real))) →
            (Ω × (Real × (Nat → Real))) × (Real × (Nat → Real))) ∘
          (MeasurableEquiv.prodAssoc :
            (Ω × (Real × (Nat → Real))) × (Real × (Nat → Real)) →
              Ω × ((Real × (Nat → Real)) × (Real × (Nat → Real)))) = id := by
      funext x
      rfl
    rw [hcomp, Measure.map_id]
  have hrotate :
      Measure.map
        (Prod.map
          (prodRotateMiddleRight (α := Ω) (β := Real) (γ := Nat → Real))
          Prod.swap)
        ((initialLaw.prod ((expMeasure leftRate).prod
          (exponentialInterarrivalMeasure leftRate))).prod
          ((expMeasure rightRate).prod (exponentialInterarrivalMeasure rightRate))) =
        ((initialLaw.prod (exponentialInterarrivalMeasure leftRate)).prod
          (expMeasure leftRate)).prod
          ((exponentialInterarrivalMeasure rightRate).prod (expMeasure rightRate)) := by
    rw [← Measure.map_prod_map _ _ measurable_prodRotateMiddleRight measurable_swap,
      map_prodRotateMiddleRight, Measure.prod_swap]
  have hmiddle :
      Measure.map
        (prodMiddleSwap
          (α := Ω × (Nat → Real)) (β := Real)
          (γ := Nat → Real) (δ := Real))
        (((initialLaw.prod (exponentialInterarrivalMeasure leftRate)).prod
          (expMeasure leftRate)).prod
          ((exponentialInterarrivalMeasure rightRate).prod (expMeasure rightRate))) =
        ((initialLaw.prod (exponentialInterarrivalMeasure leftRate)).prod
          (exponentialInterarrivalMeasure rightRate)).prod
          ((expMeasure leftRate).prod (expMeasure rightRate)) := by
    exact map_prodMiddleSwap
      (initialLaw.prod (exponentialInterarrivalMeasure leftRate))
      (expMeasure leftRate) (exponentialInterarrivalMeasure rightRate)
      (expMeasure rightRate)
  have hfinal :
      Measure.map
        (Prod.map
          (MeasurableEquiv.prodAssoc :
            (Ω × (Nat → Real)) × (Nat → Real) →
              Ω × ((Nat → Real) × (Nat → Real)))
          id)
        (((initialLaw.prod (exponentialInterarrivalMeasure leftRate)).prod
          (exponentialInterarrivalMeasure rightRate)).prod
          ((expMeasure leftRate).prod (expMeasure rightRate))) =
        (initialLaw.prod
          ((exponentialInterarrivalMeasure leftRate).prod
            (exponentialInterarrivalMeasure rightRate))).prod
          ((expMeasure leftRate).prod (expMeasure rightRate)) := by
    rw [← Measure.map_prod_map _ _ MeasurableEquiv.prodAssoc.measurable measurable_id,
      Measure.prodAssoc_prod, Measure.map_id]
  calc
    Measure.map (initialTwoStreamHeadTailRearrange (Ω := Ω))
        (initialLaw.prod
          (((expMeasure leftRate).prod (exponentialInterarrivalMeasure leftRate)).prod
            ((expMeasure rightRate).prod (exponentialInterarrivalMeasure rightRate)))) =
      Measure.map
        (Prod.map
          (MeasurableEquiv.prodAssoc :
            (Ω × (Nat → Real)) × (Nat → Real) →
              Ω × ((Nat → Real) × (Nat → Real)))
          id)
        (Measure.map
          (prodMiddleSwap
            (α := Ω × (Nat → Real)) (β := Real)
            (γ := Nat → Real) (δ := Real))
          (Measure.map
            (Prod.map
              (prodRotateMiddleRight (α := Ω) (β := Real) (γ := Nat → Real))
              Prod.swap)
            (Measure.map
              (MeasurableEquiv.prodAssoc.symm :
                Ω × ((Real × (Nat → Real)) × (Real × (Nat → Real))) →
                  (Ω × (Real × (Nat → Real))) × (Real × (Nat → Real)))
              (initialLaw.prod
                (((expMeasure leftRate).prod (exponentialInterarrivalMeasure leftRate)).prod
                  ((expMeasure rightRate).prod (exponentialInterarrivalMeasure rightRate))))))) := by
        rw [Measure.map_map
          (measurable_prodRotateMiddleRight.prodMap measurable_swap)
          MeasurableEquiv.prodAssoc.symm.measurable,
          Measure.map_map
            (measurable_prodMiddleSwap (α := Ω × (Nat → Real)) (β := Real)
              (γ := Nat → Real) (δ := Real))
            ((measurable_prodRotateMiddleRight.prodMap measurable_swap).comp
              MeasurableEquiv.prodAssoc.symm.measurable),
          Measure.map_map
            ((MeasurableEquiv.prodAssoc.measurable.prodMap measurable_id))
            ((measurable_prodMiddleSwap (α := Ω × (Nat → Real)) (β := Real)
              (γ := Nat → Real) (δ := Real)).comp
              ((measurable_prodRotateMiddleRight.prodMap measurable_swap).comp
                MeasurableEquiv.prodAssoc.symm.measurable))]
        rfl
    _ = Measure.map
        (Prod.map
          (MeasurableEquiv.prodAssoc :
            (Ω × (Nat → Real)) × (Nat → Real) →
              Ω × ((Nat → Real) × (Nat → Real)))
          id)
        (Measure.map
          (prodMiddleSwap
            (α := Ω × (Nat → Real)) (β := Real)
            (γ := Nat → Real) (δ := Real))
          (Measure.map
            (Prod.map
              (prodRotateMiddleRight (α := Ω) (β := Real) (γ := Nat → Real))
              Prod.swap)
            ((initialLaw.prod ((expMeasure leftRate).prod
              (exponentialInterarrivalMeasure leftRate))).prod
              ((expMeasure rightRate).prod (exponentialInterarrivalMeasure rightRate))))) := by
        rw [houter]
    _ = Measure.map
        (Prod.map
          (MeasurableEquiv.prodAssoc :
            (Ω × (Nat → Real)) × (Nat → Real) →
              Ω × ((Nat → Real) × (Nat → Real)))
          id)
        (Measure.map
          (prodMiddleSwap
            (α := Ω × (Nat → Real)) (β := Real)
            (γ := Nat → Real) (δ := Real))
          (((initialLaw.prod (exponentialInterarrivalMeasure leftRate)).prod
            (expMeasure leftRate)).prod
            ((exponentialInterarrivalMeasure rightRate).prod (expMeasure rightRate)))) := by
        rw [hrotate]
    _ = Measure.map
        (Prod.map
          (MeasurableEquiv.prodAssoc :
            (Ω × (Nat → Real)) × (Nat → Real) →
              Ω × ((Nat → Real) × (Nat → Real)))
          id)
        (((initialLaw.prod (exponentialInterarrivalMeasure leftRate)).prod
          (exponentialInterarrivalMeasure rightRate)).prod
          ((expMeasure leftRate).prod (expMeasure rightRate))) := by
        rw [hmiddle]
    _ = (initialLaw.prod
        ((exponentialInterarrivalMeasure leftRate).prod
          (exponentialInterarrivalMeasure rightRate))).prod
        ((expMeasure leftRate).prod (expMeasure rightRate)) := hfinal

/-- An arbitrary independent initial state, the two strictly older source
tails, and the two nearest innovations have the corresponding exact product
law.  The coordinates are not replaced by shifted copies of the source.
-/
theorem map_initialTwoStreamHeadTailFactors
    {Ω : Type*} [MeasurableSpace Ω]
    (initialLaw : Measure Ω) [IsProbabilityMeasure initialLaw]
    {leftRate rightRate : Real} (hleft : 0 < leftRate) (hright : 0 < rightRate) :
    Measure.map (initialTwoStreamHeadTailFactors (Ω := Ω))
      (initialLaw.prod
        ((exponentialInterarrivalMeasure leftRate).prod
          (exponentialInterarrivalMeasure rightRate))) =
      (initialLaw.prod
        ((exponentialInterarrivalMeasure leftRate).prod
          (exponentialInterarrivalMeasure rightRate))).prod
        ((expMeasure leftRate).prod (expMeasure rightRate)) := by
  letI : IsProbabilityMeasure (expMeasure leftRate) :=
    isProbabilityMeasure_expMeasure hleft
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure leftRate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hleft
  letI : IsProbabilityMeasure (expMeasure rightRate) :=
    isProbabilityMeasure_expMeasure hright
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rightRate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hright
  rw [show initialTwoStreamHeadTailFactors (Ω := Ω) =
      initialTwoStreamHeadTailRearrange (Ω := Ω) ∘
        Prod.map id (Prod.map headTail headTail) by
    funext x
    exact initialTwoStreamHeadTailFactors_eq_rearrange x]
  rw [← Measure.map_map measurable_initialTwoStreamHeadTailRearrange
    (measurable_id.prodMap (measurable_headTail.prodMap measurable_headTail))]
  rw [← Measure.map_prod_map _ _ measurable_id
    (measurable_headTail.prodMap measurable_headTail), Measure.map_id,
    ← Measure.map_prod_map _ _ measurable_headTail measurable_headTail,
    map_headTail_exponentialInterarrivalMeasure hleft,
    map_headTail_exponentialInterarrivalMeasure hright]
  exact map_initialTwoStreamHeadTailRearrange initialLaw hleft hright

end

end EconCSLib.Probability.PoissonProcess
