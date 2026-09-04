import QX26AgenticDelegation.MainTheorems
import QX26AgenticDelegation.Assumptions

/-!
# Human-Facing Paper Interface: Agentic Delegation and the Language Frontier of Software Developers: A Model and Evidence from Claude Code on GitHub

This is the compact Lean file a human should read after formalization to check
whether the paper's definitions and named theorem statements were represented
correctly. Keep the row-level dashboard and LLM audit statements in this file
for every paper. Move implementation details, proof aliases, and bulky helper
lemmas behind imported modules such as `AuditInterface.lean`, but expose the
audited paper-facing statements directly here; do not use
`paper_interface.audit_surface_path`.

Rules for completing this file:

- Keep the paper's definitions/formatted objects first, in source order.
- Expose the actual paper formulas here; do not only point to generic library
  definitions or implementation witnesses.
- A material reusable `EconCSLib` primitive may remain a reference here only
  after `audit/library_semantic_review.json` records its exact bounded library
  declaration and an explicit byte-pinned paper-source connection. The
  dashboard and human-review packet show and source-check that declaration
  before the dependent Spec; a library name, docstring, or glossary is not a
  semantic bridge. Do not add a duplicate paper claim merely to restate it.
- If a named theorem needs a hypothesis that is not derived from earlier Lean
  declarations, declare that hypothesis in `Assumptions.lean` and list it in
  `status.json` `review_surface.assumption_names`.
- Then state the named results directly, with assumptions visible in each
  theorem signature by referencing named paper assumptions imported from
  `Assumptions.lean`.
- In the statement-first phase, write every complete source-facing statement as
  a transparent `<name>Spec : Prop` here, exactly once. Put the paired
  theorem/lemma of that exact type in `ProofInterface.lean`; its temporary
  proof body may be `by sorry` only in a private draft. This separation keeps
  the human semantic surface free of thin wrapper declarations.
- Before drafting that Lean surface, independently inventory every material
  source atom from exact pinned source quote bytes. Do not infer source atoms
  from declaration, binder, field, function, or source-map names.
- Run raw-source-to-expanded-Spec statement matching plus recursive
  premise/conclusion provenance on the skeleton. The semantic comparison uses
  only byte-pinned source quotes (and separately pinned source context) against
  the expanded transparent Spec; map summaries and proof wrappers are not
  semantic inputs. Then freeze each canonical Lean declaration-manifest digest.
- In the proof phase, replace the `ProofInterface.lean` `sorry` with a short
  proof that calls into `MainTheorems.lean` or lower proof files without
  changing the specification or theorem type. Any specification/type change
  invalidates the freeze and requires a fresh statement audit.
- At formalized closeout, complete the v11 realization receipt: Lean Meta checks
  the theorem has exactly the transparent Spec type; each source atom is bound
  to the elaborated Spec surface; closure traversal includes proof and instance
  arguments; and every material terminal has a source, approved correction or
  additional assumption, checked derivation, or version-pinned foundation
  disposition. No data, container, or identifier-based exemption is allowed.
- The transparent `...Spec` is the sole semantic-review target for its source
  claim. The paired theorem/lemma is a proof endpoint whose exact Spec type is
  verified by Lean Meta, not a duplicate source-to-Lean comparison row.
- Keep proof endpoints, exhaustive endpoint aliases, and proof-seam checks in
  `ProofInterface.lean`, implementation modules, or `ProofLedger.lean`, not
  here. Do not create new `PostPaperAudit.lean` or `AuditLedger.lean` files;
  those names are legacy.

## Named Results

Each entry has one semantic-review target (`Spec`) and one proof endpoint (the
paired theorem/lemma). The human dashboard and review packet present that pair
once rather than treating the two declarations as duplicate paper claims.

- `paper_proposition1_frontier_expansionSpec` -> `paper_proposition1_frontier_expansion`: Proposition 1 (Frontier expansion), source.txt:3.
- `paper_proposition2_activation_bandSpec` -> `paper_proposition2_activation_band`: Proposition 2 (Activation band for unfamiliar languages), source.txt:4.
- `paper_proposition3_dynamic_cumulative_language_effectSpec` -> `paper_proposition3_dynamic_cumulative_language_effect`: Proposition 3 (Dynamic cumulative-language effect), source.txt:5.
- `paper_proposition4_specialist_and_ability_heterogeneitySpec` -> `paper_proposition4_specialist_and_ability_heterogeneity`: Proposition 4 (Specialist and ability heterogeneity), source.txt:7.
- `paper_proposition5_repository_expansionSpec` -> `paper_proposition5_repository_expansion`: Proposition 5 (Repository expansion), source.txt:8.
-/

namespace QX26AgenticDelegation

/--
Proposition 1 (Frontier expansion)

Paper statement: Proposition 1 (Frontier expansion). For every developer, language, date, and opportunity realization, Z^2_{ik,t} >= Z^1_{ik,t}, hence N^2_{it} >= N^1_{it} path by path.

Source location: source.txt:3
Source status: pinned statement-spec transcription; independent source audit pending

This transparent proposition is the exact statement-audit target. It is not
proof evidence. Its exact-type proof endpoint is declared in
`ProofInterface.lean`, so this human-facing file presents the full semantic
proposition once. At closeout, source atoms must be independently inventoried
from pinned source quote bytes and bound to this elaborated proposition rather
than inferred from identifiers.
-/
def paper_proposition1_frontier_expansionSpec : Prop :=
  ∀ {Language : Type} (languages : Finset Language)
    (solo augmentation delegation : Language → ℝ),
    (∀ language,
      (if 0 ≤ max (solo language) (augmentation language) then (1 : ℕ) else 0) ≤
        (if 0 ≤ max (max (solo language) (augmentation language)) (delegation language)
          then (1 : ℕ) else 0)) ∧
    (∑ language ∈ languages,
        if 0 ≤ max (solo language) (augmentation language) then (1 : ℕ) else 0) ≤
      ∑ language ∈ languages,
        if 0 ≤ max (max (solo language) (augmentation language)) (delegation language)
          then (1 : ℕ) else 0

/--
Proposition 2 (Activation band for unfamiliar languages)

Paper statement: Proposition 2 (Activation band for unfamiliar languages). Consider an unfamiliar language satisfying Assumption 1. If B_{ik,t} > 0, then Z^2_{ik,t}-Z^1_{ik,t} = 1{T^D_{ik,t} <= omega_{ik,t} < T^S_{ik,t}}. If the conditional opportunity CDF F_{ik,t} is continuous, the probability that delegation activates the language is F_{ik,t}(T^S_{ik,t})-F_{ik,t}(T^D_{ik,t}), and the expected language-count expansion is E[N^2_{it}-N^1_{it}] = sum_k [F_{ik,t}(T^1_{ik,t})-F_{ik,t}(T^2_{ik,t})] >= 0.

Source location: source.txt:4
Source status: pinned statement-spec transcription; independent source audit pending

This transparent proposition is the exact statement-audit target. It is not
proof evidence. Its exact-type proof endpoint is declared in
`ProofInterface.lean`, so this human-facing file presents the full semantic
proposition once. At closeout, source atoms must be independently inventoried
from pinned source quote bytes and bound to this elaborated proposition rather
than inferred from identifiers.
-/
def paper_proposition2_activation_bandSpec : Prop :=
  (∀ (opportunity soloThreshold augmentationThreshold delegationThreshold : ℝ),
      soloThreshold ≤ augmentationThreshold →
      delegationThreshold < soloThreshold →
      ((if delegationThreshold ≤ opportunity then (1 : ℤ) else 0) -
        (if soloThreshold ≤ opportunity then (1 : ℤ) else 0) =
        if delegationThreshold ≤ opportunity ∧ opportunity < soloThreshold then (1 : ℤ) else 0)) ∧
    (∀ {Ω : Type} [MeasurableSpace Ω]
      (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
      (opportunity : Ω → ℝ) (soloThreshold delegationThreshold : ℝ),
      Measurable opportunity →
      (∀ threshold : ℝ, μ (opportunity ⁻¹' ({threshold} : Set ℝ)) = 0) →
      delegationThreshold < soloThreshold →
      μ.real (opportunity ⁻¹' Set.Ico delegationThreshold soloThreshold) =
        μ.real (opportunity ⁻¹' Set.Iic soloThreshold) -
          μ.real (opportunity ⁻¹' Set.Iic delegationThreshold)) ∧
    (∀ {Language Ω : Type} [MeasurableSpace Ω]
      (languages : Finset Language)
      (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
      (opportunity : Language → Ω → ℝ)
      (generationOneThreshold delegationThreshold : Language → ℝ),
      (∀ language, Measurable (opportunity language)) →
      (∀ language threshold, μ ((opportunity language) ⁻¹' ({threshold} : Set ℝ)) = 0) →
      (∫ state, ∑ language ∈ languages,
        ((if min (generationOneThreshold language) (delegationThreshold language) ≤ opportunity language state
            then (1 : ℝ) else 0) -
         (if generationOneThreshold language ≤ opportunity language state then (1 : ℝ) else 0)) ∂μ) =
        ∑ language ∈ languages,
          (μ.real ((opportunity language) ⁻¹' Set.Iic (generationOneThreshold language)) -
           μ.real ((opportunity language) ⁻¹' Set.Iic
             (min (generationOneThreshold language) (delegationThreshold language)))) ∧
      0 ≤ ∑ language ∈ languages,
        (μ.real ((opportunity language) ⁻¹' Set.Iic (generationOneThreshold language)) -
         μ.real ((opportunity language) ⁻¹' Set.Iic
           (min (generationOneThreshold language) (delegationThreshold language)))))

/--
Proposition 3 (Dynamic cumulative-language effect)

Paper statement: Proposition 3 (Dynamic cumulative-language effect). For an initially unfamiliar language, let p^g_{ik} be the per-period first-use hazard under generation g. If p^2_{ik} >= p^1_{ik}, the expected cumulative-language effect at event-time horizon s is Delta C_i(s) = sum_{k in U_i} [(1-p^1_{ik})^(s+1) - (1-p^2_{ik})^(s+1)] >= 0, which in the closed-frontier benchmark p^1_{ik}=0<p^2_{ik} is strictly increasing and concave over the observed horizon.

Source location: source.txt:5
Source status: pinned statement-spec transcription; independent source audit pending

This transparent proposition is the exact statement-audit target. It is not
proof evidence. Its exact-type proof endpoint is declared in
`ProofInterface.lean`, so this human-facing file presents the full semantic
proposition once. At closeout, source atoms must be independently inventoried
from pinned source quote bytes and bound to this elaborated proposition rather
than inferred from identifiers.
-/
def paper_proposition3_dynamic_cumulative_language_effectSpec : Prop :=
  ∀ {Language : Type} (languages : Finset Language)
    (generationOneHazard generationTwoHazard : Language → ℝ),
    (∀ language ∈ languages,
      0 ≤ generationOneHazard language ∧
      generationOneHazard language ≤ generationTwoHazard language ∧
      generationTwoHazard language ≤ 1) →
    (∀ horizon : ℕ,
      0 ≤ ∑ language ∈ languages,
        ((1 - generationOneHazard language) ^ (horizon + 1) -
         (1 - generationTwoHazard language) ^ (horizon + 1))) ∧
    ((∀ language ∈ languages,
        generationOneHazard language = 0 ∧ 0 < generationTwoHazard language) →
      ∀ horizon : ℕ,
        (∑ language ∈ languages,
          ((1 - generationOneHazard language) ^ (horizon + 1) -
           (1 - generationTwoHazard language) ^ (horizon + 1))) <
        (∑ language ∈ languages,
          ((1 - generationOneHazard language) ^ (horizon + 2) -
           (1 - generationTwoHazard language) ^ (horizon + 2))) ∧
        (((∑ language ∈ languages,
            ((1 - generationOneHazard language) ^ (horizon + 3) -
             (1 - generationTwoHazard language) ^ (horizon + 3))) -
          (∑ language ∈ languages,
            ((1 - generationOneHazard language) ^ (horizon + 2) -
             (1 - generationTwoHazard language) ^ (horizon + 2)))) <
         ((∑ language ∈ languages,
            ((1 - generationOneHazard language) ^ (horizon + 2) -
             (1 - generationTwoHazard language) ^ (horizon + 2))) -
          (∑ language ∈ languages,
            ((1 - generationOneHazard language) ^ (horizon + 1) -
             (1 - generationTwoHazard language) ^ (horizon + 1))))))

/--
Proposition 4 (Specialist and ability heterogeneity)

Paper statement: Proposition 4 (Specialist and ability heterogeneity). Under Assumption 3, expected expansion into initially unfamiliar languages is E[E_i|a_i,U_i] = U_i p_i(a_i,A), E_i = sum_{k in U_i}(Z^2_{ik}-Z^1_{ik}). It is increasing in the stock of unfamiliar-language candidates U_i and in general ability a_i. The largest extensive-margin gains accrue to high-ability specialists.

Source location: source.txt:7
Source status: pinned statement-spec transcription; independent source audit pending

This transparent proposition is the exact statement-audit target. It is not
proof evidence. Its exact-type proof endpoint is declared in
`ProofInterface.lean`, so this human-facing file presents the full semantic
proposition once. At closeout, source atoms must be independently inventoried
from pinned source quote bytes and bound to this elaborated proposition rather
than inferred from identifiers.
-/
def paper_proposition4_specialist_and_ability_heterogeneitySpec : Prop :=
  ∀ {Language : Type} (unfamiliarLanguages : Finset Language)
    (ability : ℝ) (activationIncrement : Language → ℝ) (commonIncrement : ℝ → ℝ),
    (∀ language ∈ unfamiliarLanguages,
      activationIncrement language = commonIncrement ability) →
    (∑ language ∈ unfamiliarLanguages, activationIncrement language) =
        (unfamiliarLanguages.card : ℝ) * commonIncrement ability ∧
    (∀ (candidateStockLow candidateStockHigh : ℕ) (abilityLow abilityHigh : ℝ),
      candidateStockLow ≤ candidateStockHigh →
      abilityLow ≤ abilityHigh →
      (∀ a, 0 ≤ commonIncrement a) →
      Monotone commonIncrement →
      (candidateStockLow : ℝ) * commonIncrement abilityLow ≤
        (candidateStockHigh : ℝ) * commonIncrement abilityHigh)

/--
Proposition 5 (Repository expansion)

Paper statement: Proposition 5 (Repository expansion). Suppose each repository requires at least one programming language and carries an entry cost that is weakly decreasing when the developer can activate that language. If agentic delegation weakly expands the active-language set, then the expected number of repositories the developer can contribute to weakly increases. It increases strictly when some repositories require languages in the delegation activation band.

Source location: source.txt:8
Source status: pinned statement-spec transcription; independent source audit pending

This transparent proposition is the exact statement-audit target. It is not
proof evidence. Its exact-type proof endpoint is declared in
`ProofInterface.lean`, so this human-facing file presents the full semantic
proposition once. At closeout, source atoms must be independently inventoried
from pinned source quote bytes and bound to this elaborated proposition rather
than inferred from identifiers.
-/
def paper_proposition5_repository_expansionSpec : Prop :=
  ∀ {Repository Ω : Type} [MeasurableSpace Ω]
    (repositories : Finset Repository)
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (opportunity : Repository → Ω → ℝ)
    (generationOneCost generationTwoCost : Repository → ℝ),
    (∀ repository, Measurable (opportunity repository)) →
    (∀ repository ∈ repositories, generationTwoCost repository ≤ generationOneCost repository) →
    (∀ state,
      (∑ repository ∈ repositories,
        if generationOneCost repository ≤ opportunity repository state then (1 : ℕ) else 0) ≤
      ∑ repository ∈ repositories,
        if generationTwoCost repository ≤ opportunity repository state then (1 : ℕ) else 0) ∧
    (∫ state, ∑ repository ∈ repositories,
        if generationOneCost repository ≤ opportunity repository state then (1 : ℝ) else 0 ∂μ) ≤
      ∫ state, ∑ repository ∈ repositories,
        if generationTwoCost repository ≤ opportunity repository state then (1 : ℝ) else 0 ∂μ ∧
    ((∃ repository ∈ repositories,
        0 < μ.real ((opportunity repository) ⁻¹'
          Set.Ico (generationTwoCost repository) (generationOneCost repository))) →
      (∫ state, ∑ repository ∈ repositories,
        if generationOneCost repository ≤ opportunity repository state then (1 : ℝ) else 0 ∂μ) <
      ∫ state, ∑ repository ∈ repositories,
        if generationTwoCost repository ≤ opportunity repository state then (1 : ℝ) else 0 ∂μ)

end QX26AgenticDelegation
