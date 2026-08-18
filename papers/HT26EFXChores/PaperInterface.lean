import HT26EFXChores.MainTheorems
import HT26EFXChores.Assumptions
import HT26EFXChores.Canonical
import HT26EFXChores.TriConstruction
import HT26EFXChores.ExceptionalCombination
import HT26EFXChores.AppendixTriInstance
import HT26EFXChores.ParetoConstruction
import HT26EFXChores.FullBiValuedDispatch

/-!
# Human-Facing Paper Interface: EFX for Additive Chores: Nonexistence, Pareto Incompatibility, and Bi-Valued Existence

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
- If a named theorem needs a hypothesis that is not derived from earlier Lean
  declarations, declare that hypothesis in `Assumptions.lean` and list it in
  `status.json` `review_surface.assumption_names`.
- Then state the named results directly, with assumptions visible in each
  theorem signature by referencing named paper assumptions imported from
  `Assumptions.lean`.
- In the statement-first phase, write every complete source-facing statement as
  one transparent `<name>Spec : Prop` here. The exact-type theorem/lemma
  endpoint belongs in `ProofInterface.lean`; this keeps this file to one
  semantic declaration per source claim.
- Before drafting that Lean surface, independently inventory every material
  source atom from exact pinned source quote bytes. Do not infer source atoms
  from declaration, binder, field, function, or source-map names.
- Run the raw-source-to-expanded-Spec semantic review on the skeleton: the LLM
  receives only the byte-pinned source-anchor bundle (including any separately
  pinned source context) and the elaborated transparent `...Spec : Prop`.
  Source-map summaries, declaration names, and prose translations are locators
  or display aids, never semantic-review input. Then freeze each canonical Lean
  declaration-manifest digest.
- In the proof phase, replace the endpoint proof in `ProofInterface.lean`
  without changing this specification. Any specification/type change
  invalidates the freeze and requires a fresh statement audit.
- At formalized closeout, complete the v11 realization receipt: Lean Meta checks
  the theorem has exactly the transparent Spec type; each source atom is bound
  to the elaborated Spec surface; closure traversal includes proof and instance
  arguments; and every material terminal has a source, approved correction or
  additional assumption, checked derivation, or version-pinned foundation
  disposition. No data, container, or identifier-based exemption is allowed.
- The `...Spec` declaration is the sole semantic target for a source claim. Its
  paired theorem/lemma is the Lean proof endpoint, checked only for having that
  exact type; it is not a second source-to-Lean comparison row.
- Keep exhaustive endpoint aliases and proof-seam checks in implementation
  modules, `ProofInterface.lean`, or `ProofLedger.lean`, not here. Do not create
  new `PostPaperAudit.lean` or `AuditLedger.lean` files; those names are legacy.

## Named Results

Each entry below is one semantic-review target (`Spec`). The dashboard and
human-review packet name the separately checked proof endpoint as evidence,
without adding a duplicate semantic claim.

- `envyFreeForChores_iff_source_definitionSpec`: displayed EF-for-chores definition, EFXadditivechores.tex:253-255.
- `efxForChores_iff_source_definitionSpec`: displayed EFX-for-chores definition, EFXadditivechores.tex:260-275.
- `paretoOptimalForChores_iff_source_definitionSpec`: displayed Pareto-optimality definition, EFXadditivechores.tex:280-287.
- `canonicalSmallChoreAllocation_iff_source_definitionSpec`: displayed canonical-allocation definition, EFXadditivechores.tex:752.
- `canonicalShortLongLabels_iff_source_definitionSpec`: displayed canonical short/long-label convention, EFXadditivechores.tex:753-754.
- `superCanonicalSmallChoreAllocation_iff_source_definitionSpec`: displayed super-canonical-allocation definition, EFXadditivechores.tex:755.
- `tri_valued_nonexistenceSpec`: Theorem 1 (tri-valued EFX nonexistence), EFXadditivechores.tex:304-306.
- `tri_four_no_two_largeSpec`: Four-agent construction proposition: at most one A item per bundle, EFXadditivechores.tex:340-342.
- `tri_four_no_a_bundle_expensiveSpec`: Four-agent construction proposition: no-A bundle is expensive, EFXadditivechores.tex:363-365.
- `efx_pareto_incompatibilitySpec`: Theorem 2 (EFX and Pareto-optimality incompatibility), EFXadditivechores.tex:416-418.
- `efx_po_every_agent_largeSpec`: Theorem 2 proposition: every EFX agent receives a large item, EFXadditivechores.tex:461-463.
- `efx_po_cost_lower_boundsSpec`: Theorem 2 proposition: EFX cost lower bounds, EFXadditivechores.tex:502-504.
- `four_agent_bi_valued_efx_existsSpec`: Theorem 3 (four-agent bi-valued EFX existence), EFXadditivechores.tex:532-534.
- `m34_insertionSpec`: Lemma (M34 insertion), EFXadditivechores.tex:577-580.
- `compositionSpec`: Lemma (composition), EFXadditivechores.tex:706-725.
- `canonical_allocation_propertiesSpec`: Lemma (canonical allocation properties), EFXadditivechores.tex:760-770.
- `balanced_orientationSpec`: Lemma (balanced orientation), EFXadditivechores.tex:1019-1034.
- `m2_efx_allocationSpec`: Lemma (EFX allocation of M2), EFXadditivechores.tex:1045-1047.
- `m2_efx_allocation_propertiesSpec`: Lemma (properties of the M2 EFX allocations), EFXadditivechores.tex:1419-1462.
- `exceptional_residue_combinationSpec`: Lemma (exceptional-residue combination), EFXadditivechores.tex:1709-1713.
- `appendix_no_two_a_itemsSpec`: Appendix A proposition: no bundle contains two A items, EFXadditivechores.tex:2074-2076.
- `appendix_p1_p2_lower_boundsSpec`: Appendix A proposition: p1 and p2 lower bounds, EFXadditivechores.tex:2104-2106.
-/

namespace HT26EFXChores

/-- The source's displayed envy-free-for-chores definition. -/
def envyFreeForChores_iff_source_definitionSpec : Prop :=
  ∀ (Agent Item : Type) (cost : Agent → EconCSLib.FairDivision.Bundle Item → ℝ)
    (allocation : EconCSLib.FairDivision.Allocation Agent Item),
    EconCSLib.FairDivision.EnvyFreeForChores cost allocation ↔
      ∀ i j, cost i (allocation i) ≤ cost i (allocation j)


/-- The source's displayed EFX-for-chores definition, including its
empty-own-bundle alternative. -/
def efxForChores_iff_source_definitionSpec : Prop :=
  by
  classical
  exact ∀ (Agent Item : Type)
    (cost : Agent → EconCSLib.FairDivision.Bundle Item → ℝ)
    (allocation : EconCSLib.FairDivision.Allocation Agent Item),
    EconCSLib.FairDivision.EFXForChores cost allocation ↔
      ∀ i j, allocation i = ∅ ∨
        ∀ item ∈ allocation i, cost i (allocation i \ {item}) ≤ cost i (allocation j)


/-- The source's Pareto-optimality definition on complete chore allocations. -/
def paretoOptimalForChores_iff_source_definitionSpec : Prop :=
  by
  classical
  exact ∀ (Agent Item : Type)
    (cost : Agent → EconCSLib.FairDivision.Bundle Item → ℝ)
    (chores : Finset Item) (allocation : EconCSLib.FairDivision.Allocation Agent Item),
    EconCSLib.FairDivision.IsAllocationOf allocation chores →
      (EconCSLib.FairDivision.ParetoOptimalForChores cost chores allocation ↔
        ¬ ∃ improvement : EconCSLib.FairDivision.Allocation Agent Item,
          EconCSLib.FairDivision.IsAllocationOf improvement chores ∧
            (∀ i, cost i (improvement i) ≤ cost i (allocation i)) ∧
              ∃ i, cost i (improvement i) < cost i (allocation i))


/--
The source's canonical-allocation definition.  The right side is the paper
formula itself: a complete allocation of the four-agent M01 pool, with each
bundle of size `a` or `a + 1` and containing the maximum possible number of
items uniquely small for its owner.  The left side records the reusable quota
implementation and makes the implementation/source bridge explicit.
-/
def canonicalSmallChoreAllocation_iff_source_definitionSpec : Prop :=
  by
  classical
  exact ∀ (Item : Type) (r : ℝ)
    (cost : EconCSLib.FairDivision.ChoreCost (Fin 4) Item) (chores : Finset Item)
    (a b : ℕ) (allocation : EconCSLib.FairDivision.Allocation (Fin 4) Item),
    2 < r →
      EconCSLib.FairDivision.IsOneOrRChoreCost cost r →
        b ≤ 3 →
          chores.card = 4 * a + b →
            (∀ item ∈ chores, EconCSLib.FairDivision.IsSmallForAtMostOne cost item) →
              ((∃ quota : Fin 4 → ℕ,
                (∀ agent, quota agent = a ∨ quota agent = a + 1) ∧
                  EconCSLib.FairDivision.IsCanonicalSmallChoreAllocation
                    cost chores quota allocation) ↔
                (EconCSLib.FairDivision.IsAllocationOf allocation chores ∧
                  ∀ agent,
                    ((allocation agent).card = a ∨
                      (allocation agent).card = a + 1) ∧
                      (EconCSLib.FairDivision.ownSmallChoreSet
                        cost (allocation agent) agent).card =
                        min (allocation agent).card
                          (EconCSLib.FairDivision.ownSmallChoreSet
                            cost chores agent).card))


/--
The source's short/long-label convention for a canonical allocation.

The label sets are made explicit rather than absorbed into the canonical
allocation definition: for `b > 0`, the short (respectively long) agents are
exactly those receiving `a` (respectively `a + 1`) items; for `b = 0` and
`a > 0`, every agent has both labels.  The direct canonical-allocation premise
keeps the convention in precisely the source's stated scope.
-/
def canonicalShortLongLabels_iff_source_definitionSpec : Prop :=
  by
  classical
  exact ∀ (Item : Type) (r : ℝ)
    (cost : EconCSLib.FairDivision.ChoreCost (Fin 4) Item) (chores : Finset Item)
    (a b : ℕ) (allocation : EconCSLib.FairDivision.Allocation (Fin 4) Item),
    2 < r →
      EconCSLib.FairDivision.IsOneOrRChoreCost cost r →
        b ≤ 3 →
          chores.card = 4 * a + b →
            (∀ item ∈ chores, EconCSLib.FairDivision.IsSmallForAtMostOne cost item) →
              (EconCSLib.FairDivision.IsAllocationOf allocation chores ∧
                ∀ agent,
                  ((allocation agent).card = a ∨
                    (allocation agent).card = a + 1) ∧
                      (EconCSLib.FairDivision.ownSmallChoreSet
                        cost (allocation agent) agent).card =
                        min (allocation agent).card
                          (EconCSLib.FairDivision.ownSmallChoreSet
                            cost chores agent).card) →
                ∃ shortAgents longAgents : Finset (Fin 4),
                  (0 < b →
                    (∀ agent, agent ∈ shortAgents ↔ (allocation agent).card = a) ∧
                      (∀ agent, agent ∈ longAgents ↔
                        (allocation agent).card = a + 1)) ∧
                    (b = 0 → 0 < a →
                      shortAgents = Finset.univ ∧ longAgents = Finset.univ)


/--
The source's super-canonical-allocation definition.  This keeps the source's
own cardinality-based short/long labels on the expanded right side; the left
side uses the reusable generic relation with those same sets made explicit.
-/
def superCanonicalSmallChoreAllocation_iff_source_definitionSpec : Prop :=
  by
  classical
  exact ∀ (Item : Type) (r : ℝ)
    (cost : EconCSLib.FairDivision.ChoreCost (Fin 4) Item) (chores : Finset Item)
    (a b : ℕ) (allocation : EconCSLib.FairDivision.Allocation (Fin 4) Item),
    2 < r →
      EconCSLib.FairDivision.IsOneOrRChoreCost cost r →
        0 < b →
          b ≤ 3 →
            chores.card = 4 * a + b →
              (∀ item ∈ chores, EconCSLib.FairDivision.IsSmallForAtMostOne cost item) →
                ((∃ quota : Fin 4 → ℕ,
                  (∀ agent, quota agent = a ∨ quota agent = a + 1) ∧
                    EconCSLib.FairDivision.IsSuperCanonicalSmallChoreAllocation
                      r cost chores
                      (Finset.univ.filter fun agent => quota agent = a)
                      (Finset.univ.filter fun agent => quota agent = a + 1)
                      quota allocation) ↔
                  (EconCSLib.FairDivision.IsAllocationOf allocation chores ∧
                    (∀ agent,
                      ((allocation agent).card = a ∨
                        (allocation agent).card = a + 1) ∧
                        (EconCSLib.FairDivision.ownSmallChoreSet
                          cost (allocation agent) agent).card =
                          min (allocation agent).card
                            (EconCSLib.FairDivision.ownSmallChoreSet
                              cost chores agent).card) ∧
                    ∀ shortAgent longAgent,
                      (allocation shortAgent).card = a →
                        (allocation longAgent).card = a + 1 →
                          EconCSLib.FairDivision.additiveChoreCost
                            cost shortAgent (allocation shortAgent) ≤
                            EconCSLib.FairDivision.additiveChoreCost
                              cost shortAgent (allocation longAgent) - r))


/--
Theorem 1 (tri-valued EFX nonexistence)

Paper statement: For every n at least four, a tri-valued additive chore instance with n agents has no EFX allocation.

Source location: EFXadditivechores.tex:304-306
Source status: source-first audit completed

This transparent proposition is the exact statement-audit target. It is not
proof evidence; `tri_valued_nonexistence` must remain a theorem/lemma of exactly this
type and is proved by its paired theorem/lemma. At closeout, its
source atoms must be independently inventoried from pinned source quote bytes
and bound to this elaborated proposition rather than inferred from identifiers.
-/
def tri_valued_nonexistenceSpec : Prop :=
  ∀ n : ℕ, 4 ≤ n → ∃ (Item : Type) (itemDecidableEq : DecidableEq Item)
    (choreInstance : EconCSLib.FairDivision.AdditiveChoreInstance (Fin n) Item),
    EconCSLib.FairDivision.IsTriValuedChoreCost choreInstance.cost ∧
      ∀ allocation : EconCSLib.FairDivision.Allocation (Fin n) Item,
        @EconCSLib.FairDivision.AdditiveChoreInstance.IsFeasible _ Item itemDecidableEq
            choreInstance allocation →
          ¬ @EconCSLib.FairDivision.AdditiveChoreInstance.IsEFX _ Item itemDecidableEq
            choreInstance allocation


/--
Four-agent construction proposition: at most one A item per bundle

Paper statement: In an EFX allocation of the displayed four-agent construction, no agent receives more than one A item.

Source location: EFXadditivechores.tex:340-342
Source status: source-first audit completed

This transparent proposition is the exact statement-audit target. It is not
proof evidence; `tri_four_no_two_large` must remain a theorem/lemma of exactly this
type and is proved by its paired theorem/lemma. At closeout, its
source atoms must be independently inventoried from pinned source quote bytes
and bound to this elaborated proposition rather than inferred from identifiers.
-/
def tri_four_no_two_largeSpec : Prop :=
  ∀ allocation : EconCSLib.FairDivision.Allocation (Fin 4) (Fin 13), EconCSLib.FairDivision.IsAllocationOf allocation (Finset.univ : Finset (Fin 13)) → EconCSLib.FairDivision.EFXForChores (EconCSLib.FairDivision.additiveChoreCost (fun (agent : Fin 4) (item : Fin 13) => if item.val < 3 then 20 else if agent.val < 2 then if item.val < 8 then 1 else 7 else if item.val < 8 then 7 else 1)) allocation → ∀ (agent : Fin 4), ((allocation agent).filter fun item => item.val < 3).card ≤ 1


/--
Four-agent construction proposition: no-A bundle is expensive

Paper statement: If one bundle has no A item and every other bundle has one, every agent values that bundle at least 20.

Source location: EFXadditivechores.tex:363-365
Source status: source-first audit completed

This transparent proposition is the exact statement-audit target. It is not
proof evidence; `tri_four_no_a_bundle_expensive` must remain a theorem/lemma of exactly this
type and is proved by its paired theorem/lemma. At closeout, its
source atoms must be independently inventoried from pinned source quote bytes
and bound to this elaborated proposition rather than inferred from identifiers.
-/
def tri_four_no_a_bundle_expensiveSpec : Prop :=
  ∀ allocation : EconCSLib.FairDivision.Allocation (Fin 4) (Fin 13), EconCSLib.FairDivision.IsAllocationOf allocation (Finset.univ : Finset (Fin 13)) → EconCSLib.FairDivision.EFXForChores (EconCSLib.FairDivision.additiveChoreCost (fun (agent : Fin 4) (item : Fin 13) => if item.val < 3 then 20 else if agent.val < 2 then if item.val < 8 then 1 else 7 else if item.val < 8 then 7 else 1)) allocation → ((allocation 0).filter fun item => item.val < 3).card = 0 → (∀ (agent : Fin 4), agent ≠ 0 → ((allocation agent).filter fun item => item.val < 3).card = 1) → ∀ (agent : Fin 4), 20 ≤ EconCSLib.FairDivision.additiveChoreCost (fun (agent : Fin 4) (item : Fin 13) => if item.val < 3 then 20 else if agent.val < 2 then if item.val < 8 then 1 else 7 else if item.val < 8 then 7 else 1) agent (allocation 0)


/--
Theorem 2 (EFX and Pareto-optimality incompatibility)

Paper statement: For every n at least four and sufficiently large r, a positive (1,r)-valued instance has no EFX and Pareto-optimal allocation.

Source location: EFXadditivechores.tex:416-418
Source status: source-first audit completed

This transparent proposition is the exact statement-audit target. It is not
proof evidence; `efx_pareto_incompatibility` must remain a theorem/lemma of exactly this
type and is proved by its paired theorem/lemma. At closeout, its
source atoms must be independently inventoried from pinned source quote bytes
and bound to this elaborated proposition rather than inferred from identifiers.
-/
def efx_pareto_incompatibilitySpec : Prop :=
  ∀ n : ℕ, 4 ≤ n → ∀ r : ℝ, (((n + 1) / 2 : ℕ) : ℝ) + 1 < r →
    ∃ (Item : Type) (itemDecidableEq : DecidableEq Item)
      (choreInstance : EconCSLib.FairDivision.AdditiveChoreInstance (Fin n) Item),
      EconCSLib.FairDivision.IsOneOrRChoreCost choreInstance.cost r ∧
        ∀ allocation : EconCSLib.FairDivision.Allocation (Fin n) Item,
          @EconCSLib.FairDivision.AdditiveChoreInstance.IsFeasible _ Item itemDecidableEq
              choreInstance allocation →
            @EconCSLib.FairDivision.AdditiveChoreInstance.IsEFX _ Item itemDecidableEq
              choreInstance allocation →
              ¬ @EconCSLib.FairDivision.AdditiveChoreInstance.IsParetoOptimal _ Item itemDecidableEq
                choreInstance allocation


/--
Theorem 2 proposition: every EFX agent receives a large item

Paper statement: In the Theorem 2 construction, every agent receives a large chore in an EFX allocation.

Source location: EFXadditivechores.tex:461-463
Source status: source-first audit completed

This transparent proposition is the exact statement-audit target. It is not
proof evidence; `efx_po_every_agent_large` must remain a theorem/lemma of exactly this
type and is proved by its paired theorem/lemma. At closeout, its
source atoms must be independently inventoried from pinned source quote bytes
and bound to this elaborated proposition rather than inferred from identifiers.
-/
def efx_po_every_agent_largeSpec : Prop :=
  ∀ n : ℕ, 4 ≤ n → ∀ r : ℝ, (((n + 1) / 2 : ℕ) : ℝ) + 1 < r → ∀ allocation : EconCSLib.FairDivision.Allocation (Fin n) (Fin (2 * n + 1)), EconCSLib.FairDivision.IsAllocationOf allocation (Finset.univ : Finset (Fin (2 * n + 1))) → EconCSLib.FairDivision.EFXForChores (EconCSLib.FairDivision.additiveChoreCost (fun (agent : Fin n) (item : Fin (2 * n + 1)) => if item.val < n - 1 then r else if agent.val < n / 2 then if item.val < n + n / 2 then 1 else r else if item.val < n + n / 2 then r else 1)) allocation → ∀ (agent : Fin n), ∃ item : Fin (2 * n + 1), item ∈ allocation agent ∧ (if item.val < n - 1 then r else if agent.val < n / 2 then if item.val < n + n / 2 then 1 else r else if item.val < n + n / 2 then r else 1) = r


/--
Theorem 2 proposition: EFX cost lower bounds

Paper statement: In the Theorem 2 construction, every EFX bundle costs at least r+1 to its owner and one costs at least r+2.

Source location: EFXadditivechores.tex:502-504
Source status: source-first audit completed

This transparent proposition is the exact statement-audit target. It is not
proof evidence; `efx_po_cost_lower_bounds` must remain a theorem/lemma of exactly this
type and is proved by its paired theorem/lemma. At closeout, its
source atoms must be independently inventoried from pinned source quote bytes
and bound to this elaborated proposition rather than inferred from identifiers.
-/
def efx_po_cost_lower_boundsSpec : Prop :=
  ∀ n : ℕ, 4 ≤ n → ∀ r : ℝ, (((n + 1) / 2 : ℕ) : ℝ) + 1 < r → ∀ allocation : EconCSLib.FairDivision.Allocation (Fin n) (Fin (2 * n + 1)), EconCSLib.FairDivision.IsAllocationOf allocation (Finset.univ : Finset (Fin (2 * n + 1))) → EconCSLib.FairDivision.EFXForChores (EconCSLib.FairDivision.additiveChoreCost (fun (agent : Fin n) (item : Fin (2 * n + 1)) => if item.val < n - 1 then r else if agent.val < n / 2 then if item.val < n + n / 2 then 1 else r else if item.val < n + n / 2 then r else 1)) allocation → (∀ (agent : Fin n), r + 1 ≤ EconCSLib.FairDivision.additiveChoreCost (fun (agent : Fin n) (item : Fin (2 * n + 1)) => if item.val < n - 1 then r else if agent.val < n / 2 then if item.val < n + n / 2 then 1 else r else if item.val < n + n / 2 then r else 1) agent (allocation agent)) ∧ ∃ (agent : Fin n), r + 2 ≤ EconCSLib.FairDivision.additiveChoreCost (fun (agent : Fin n) (item : Fin (2 * n + 1)) => if item.val < n - 1 then r else if agent.val < n / 2 then if item.val < n + n / 2 then 1 else r else if item.val < n + n / 2 then r else 1) agent (allocation agent)


/--
Theorem 3 (four-agent bi-valued EFX existence)

Paper statement: Every four-agent bi-valued chore instance admits an EFX allocation.

Source location: EFXadditivechores.tex:532-534
Source status: source-first audit completed

This transparent proposition is the exact statement-audit target. It is not
proof evidence; `four_agent_bi_valued_efx_exists` must remain a theorem/lemma of exactly this
type and is proved by its paired theorem/lemma. At closeout, its
source atoms must be independently inventoried from pinned source quote bytes
and bound to this elaborated proposition rather than inferred from identifiers.
-/
def four_agent_bi_valued_efx_existsSpec : Prop :=
  by
  classical
  exact ∀ (Item : Type) (choreInstance : EconCSLib.FairDivision.AdditiveChoreInstance (Fin 4) Item),
    EconCSLib.FairDivision.IsBiValuedChoreCost choreInstance.cost →
    ∃ allocation : EconCSLib.FairDivision.Allocation (Fin 4) Item,
      choreInstance.IsFeasible allocation ∧ choreInstance.IsEFX allocation


/--
Lemma (M34 insertion)

Paper statement: An item small for at least three agents can be inserted into an EFX allocation of the remaining chores.

Source location: EFXadditivechores.tex:577-580
Source status: source-first audit completed

This transparent proposition is the exact statement-audit target. It is not
proof evidence; `m34_insertion` must remain a theorem/lemma of exactly this
type and is proved by its paired theorem/lemma. At closeout, its
source atoms must be independently inventoried from pinned source quote bytes
and bound to this elaborated proposition rather than inferred from identifiers.
-/
def m34_insertionSpec : Prop :=
  by
  classical
  exact ∀ (Item : Type) (r : ℝ) (cost : EconCSLib.FairDivision.ChoreCost (Fin 4) Item) (chores : Finset Item) (item : Item), 2 < r → EconCSLib.FairDivision.IsOneOrRChoreCost cost r → item ∉ chores → EconCSLib.FairDivision.IsSmallForAtLeastThree cost item → ∀ allocation : EconCSLib.FairDivision.Allocation (Fin 4) Item, EconCSLib.FairDivision.IsAllocationOf allocation chores → EconCSLib.FairDivision.EFXForChores (EconCSLib.FairDivision.additiveChoreCost cost) allocation → ∃ extended : EconCSLib.FairDivision.Allocation (Fin 4) Item, EconCSLib.FairDivision.IsAllocationOf extended (insert item chores) ∧ EconCSLib.FairDivision.EFXForChores (EconCSLib.FairDivision.additiveChoreCost cost) extended


/--
Lemma (composition)

Paper statement: The stated cost-gap conditions combine two allocations into an EFX allocation.

Source location: EFXadditivechores.tex:706-725
Source status: source-first audit completed

This transparent proposition is the exact statement-audit target. It is not
proof evidence; `composition` must remain a theorem/lemma of exactly this
type and is proved by its paired theorem/lemma. At closeout, its
source atoms must be independently inventoried from pinned source quote bytes
and bound to this elaborated proposition rather than inferred from identifiers.
-/
def compositionSpec : Prop :=
  by
  classical
  exact ∀ (Agent Item : Type) (cost : EconCSLib.FairDivision.ChoreCost Agent Item) (leftChores rightChores : Finset Item) (leftAllocation rightAllocation : EconCSLib.FairDivision.Allocation Agent Item), Disjoint leftChores rightChores → EconCSLib.FairDivision.IsAllocationOf leftAllocation leftChores → EconCSLib.FairDivision.IsAllocationOf rightAllocation rightChores → (∀ agent item, 1 ≤ cost agent item) → EconCSLib.FairDivision.IsAllocationOf (fun agent => leftAllocation agent ∪ rightAllocation agent) (leftChores ∪ rightChores) ∧ ((EconCSLib.FairDivision.EnvyFreeForChores (EconCSLib.FairDivision.additiveChoreCost cost) leftAllocation ∧ ∀ i j, EconCSLib.FairDivision.additiveChoreCost cost i (rightAllocation i) - 1 ≤ EconCSLib.FairDivision.additiveChoreCost cost i (rightAllocation j)) → EconCSLib.FairDivision.EFXForChores (EconCSLib.FairDivision.additiveChoreCost cost) (fun agent => leftAllocation agent ∪ rightAllocation agent)) ∧ ((∀ i j (hnonempty : (leftAllocation i ∪ rightAllocation i).Nonempty), EconCSLib.FairDivision.additiveChoreCost cost i (leftAllocation i) - EconCSLib.FairDivision.additiveChoreCost cost i (leftAllocation j) ≤ EconCSLib.FairDivision.additiveChoreCost cost i (rightAllocation j) - EconCSLib.FairDivision.additiveChoreCost cost i (rightAllocation i) + ((leftAllocation i ∪ rightAllocation i).image (cost i)).min' (Finset.image_nonempty.mpr hnonempty)) → EconCSLib.FairDivision.EFXForChores (EconCSLib.FairDivision.additiveChoreCost cost) (fun agent => leftAllocation agent ∪ rightAllocation agent)) ∧ (∀ i j (hnonempty : (leftAllocation i ∪ rightAllocation i).Nonempty), EconCSLib.FairDivision.additiveChoreCost cost i (leftAllocation i) - EconCSLib.FairDivision.additiveChoreCost cost i (leftAllocation j) ≤ EconCSLib.FairDivision.additiveChoreCost cost i (rightAllocation j) - EconCSLib.FairDivision.additiveChoreCost cost i (rightAllocation i) + ((leftAllocation i ∪ rightAllocation i).image (cost i)).min' (Finset.image_nonempty.mpr hnonempty) → EconCSLib.FairDivision.DoesNotStronglyEnvyForChores (EconCSLib.FairDivision.additiveChoreCost cost) (fun agent => leftAllocation agent ∪ rightAllocation agent) i j)


/--
Lemma (canonical allocation properties)

Paper statement: Canonical M01 allocations are EFX, equal-quota canonical allocations are envy-free, and the stated super-canonical allocations exist.

Source location: EFXadditivechores.tex:760-770
Source status: source-first audit completed

This transparent proposition is the exact statement-audit target. It is not
proof evidence; `canonical_allocation_properties` must remain a theorem/lemma of exactly this
type and is proved by its paired theorem/lemma. At closeout, its
source atoms must be independently inventoried from pinned source quote bytes
and bound to this elaborated proposition rather than inferred from identifiers.
-/
def canonical_allocation_propertiesSpec : Prop :=
  by
  classical
  exact ∀ (Item : Type) (r : ℝ) (cost : EconCSLib.FairDivision.ChoreCost (Fin 4) Item) (chores : Finset Item) (a b : ℕ), 2 < r → EconCSLib.FairDivision.IsOneOrRChoreCost cost r → b ≤ 3 → chores.card = 4 * a + b → (∀ item ∈ chores, EconCSLib.FairDivision.IsSmallForAtMostOne cost item) → ((∀ quota allocation, (∀ agent, quota agent = a ∨ quota agent = a + 1) → EconCSLib.FairDivision.IsCanonicalSmallChoreAllocation cost chores quota allocation → EconCSLib.FairDivision.EFXForChores (EconCSLib.FairDivision.additiveChoreCost cost) allocation) ∧ (b = 0 → ∀ quota allocation, (∀ agent, quota agent = a) → EconCSLib.FairDivision.IsCanonicalSmallChoreAllocation cost chores quota allocation → EconCSLib.FairDivision.EnvyFreeForChores (EconCSLib.FairDivision.additiveChoreCost cost) allocation) ∧ (0 < b → ∃ quota allocation, (∀ agent, quota agent = a ∨ quota agent = a + 1) ∧ EconCSLib.FairDivision.IsCanonicalSmallChoreAllocation cost chores quota allocation ∧ ∀ i j, quota i = a → quota j = a + 1 → EconCSLib.FairDivision.additiveChoreCost cost i (allocation i) ≤ EconCSLib.FairDivision.additiveChoreCost cost i (allocation j) - r) ∧ (0 < a → b = 2 → ∀ N1 N2 : Finset (Fin 4), N1 ∪ N2 = Finset.univ → Disjoint N1 N2 → N1.card = 2 → N2.card = 2 → ∃ i ∈ N1, ∃ j ∈ N2, ∃ quota allocation, (∀ agent, quota agent = a ∨ quota agent = a + 1) ∧ EconCSLib.FairDivision.IsCanonicalSmallChoreAllocation cost chores quota allocation ∧ (∀ x y, quota x = a → quota y = a + 1 → EconCSLib.FairDivision.additiveChoreCost cost x (allocation x) ≤ EconCSLib.FairDivision.additiveChoreCost cost x (allocation y) - r) ∧ quota i = a ∧ quota j = a))


/--
Lemma (balanced orientation)

Paper statement: A multigraph has an endpoint assignment with prescribed indegrees exactly when every vertex-set demand is at most its incident-edge count; the partial version allows unassigned edges.

Source location: EFXadditivechores.tex:1019-1034
Source status: source-first audit completed

This transparent proposition is the exact statement-audit target. It is not
proof evidence; `balanced_orientation` must remain a theorem/lemma of exactly this
type and is proved by its paired theorem/lemma. At closeout, its
source atoms must be independently inventoried from pinned source quote bytes
and bound to this elaborated proposition rather than inferred from identifiers.
-/
def balanced_orientationSpec : Prop :=
  by
  classical
  exact ∀ (Vertex Edge : Type) [Fintype Vertex] (edges : Finset Edge)
    (endpoints : Edge → Finset Vertex) (quota : Vertex → ℕ),
    (∀ edge ∈ edges, (endpoints edge).card = 2) →
      (Finset.univ.sum quota = edges.card →
        ((∃ owner : Edge → Option Vertex,
            (∀ edge ∈ edges, ∃ vertex, owner edge = some vertex ∧ vertex ∈ endpoints edge) ∧
              ∀ vertex, (edges.filter fun edge => owner edge = some vertex).card = quota vertex) ↔
          ∀ vertices : Finset Vertex,
            vertices.sum quota ≤
              (edges.filter fun edge => (endpoints edge ∩ vertices).Nonempty).card)) ∧
      (Finset.univ.sum quota ≤ edges.card →
        (∀ vertices : Finset Vertex,
          vertices.sum quota ≤
            (edges.filter fun edge => (endpoints edge ∩ vertices).Nonempty).card) →
          ∃ owner : Edge → Option Vertex,
            (∀ edge ∈ edges, ∀ vertex, owner edge = some vertex → vertex ∈ endpoints edge) ∧
              ∀ vertex, (edges.filter fun edge => owner edge = some vertex).card = quota vertex)


/--
Lemma (EFX allocation of M2)

Paper statement: Every four-agent pool in which every item is small for exactly two agents admits an EFX allocation.

Source location: EFXadditivechores.tex:1045-1047
Source status: source-first audit completed

This transparent proposition is the exact statement-audit target. It is not
proof evidence; `m2_efx_allocation` must remain a theorem/lemma of exactly this
type and is proved by its paired theorem/lemma. At closeout, its
source atoms must be independently inventoried from pinned source quote bytes
and bound to this elaborated proposition rather than inferred from identifiers.
-/
def m2_efx_allocationSpec : Prop :=
  by
  classical
  exact ∀ (Item : Type) (r : ℝ) (cost : EconCSLib.FairDivision.ChoreCost (Fin 4) Item) (chores : Finset Item), 2 < r → EconCSLib.FairDivision.IsOneOrRChoreCost cost r → (∀ item ∈ chores, EconCSLib.FairDivision.IsSmallForExactlyTwo cost item) → ∃ allocation : EconCSLib.FairDivision.Allocation (Fin 4) Item, EconCSLib.FairDivision.IsAllocationOf allocation chores ∧ EconCSLib.FairDivision.EFXForChores (EconCSLib.FairDivision.additiveChoreCost cost) allocation


/--
Lemma (properties of the M2 EFX allocations)

Paper statement: The M2 EFX allocation can be chosen with the stated small-item certificates, exceptional-residue alternatives, and preferred endpoint envy-free property.

Source location: EFXadditivechores.tex:1419-1462
Source status: source-first audit completed

This transparent proposition is the exact statement-audit target. It is not
proof evidence; `m2_efx_allocation_properties` must remain a theorem/lemma of exactly this
type and is proved by its paired theorem/lemma. At closeout, its
source atoms must be independently inventoried from pinned source quote bytes
and bound to this elaborated proposition rather than inferred from identifiers.
-/
def m2_efx_allocation_propertiesSpec : Prop :=
  by
  classical
  exact ∀ (Item : Type) (r : ℝ)
    (cost : EconCSLib.FairDivision.ChoreCost (Fin 4) Item) (chores : Finset Item),
    2 < r →
      EconCSLib.FairDivision.IsOneOrRChoreCost cost r →
        (∀ item ∈ chores, EconCSLib.FairDivision.IsSmallForExactlyTwo cost item) →
          ∃ allocation : EconCSLib.FairDivision.Allocation (Fin 4) Item,
            EconCSLib.FairDivision.IsAllocationOf allocation chores ∧
              EconCSLib.FairDivision.EFXForChores
                (EconCSLib.FairDivision.additiveChoreCost cost) allocation ∧
              (¬ (∃ dominant auxiliary : Finset (Fin 4), ∃ q : ℕ,
                dominant.card = 2 ∧ auxiliary.card = 2 ∧ Disjoint dominant auxiliary ∧
                  (((∀ item ∈ chores,
                    EconCSLib.FairDivision.smallAgentSet cost item = dominant) ∧
                    chores.card = 4 * q + 3) ∨
                    (∃ exceptionalItem ∈ chores,
                      EconCSLib.FairDivision.smallAgentSet cost exceptionalItem = auxiliary ∧
                      (∀ item ∈ chores.erase exceptionalItem,
                        EconCSLib.FairDivision.smallAgentSet cost item = dominant) ∧
                      (chores.erase exceptionalItem).card = 4 * q + 3))) →
                (∀ i, (∃ item ∈ allocation i,
                  EconCSLib.FairDivision.IsSmallChore cost i item) → ∀ j,
                    EconCSLib.FairDivision.additiveChoreCost cost i (allocation i) - 1 ≤
                      EconCSLib.FairDivision.additiveChoreCost cost i (allocation j)) ∧
                (∀ i, (∀ item ∈ allocation i,
                  EconCSLib.FairDivision.IsLargeChore cost r i item) → ∀ j,
                    EconCSLib.FairDivision.additiveChoreCost cost i (allocation i) ≤
                      EconCSLib.FairDivision.additiveChoreCost cost i (allocation j))) ∧
              (∀ firstType secondType : Finset (Fin 4),
                firstType.card = 2 → secondType.card = 2 → Disjoint firstType secondType →
                  (∀ item ∈ chores,
                    EconCSLib.FairDivision.smallAgentSet cost item = firstType ∨
                      EconCSLib.FairDivision.smallAgentSet cost item = secondType) →
                  (chores.filter fun item =>
                    EconCSLib.FairDivision.smallAgentSet cost item = secondType).card ≥
                    (chores.filter fun item =>
                      EconCSLib.FairDivision.smallAgentSet cost item = firstType).card →
                    ∀ agent ∈ firstType,
                      ∃ preferredAllocation : EconCSLib.FairDivision.Allocation (Fin 4) Item,
                        EconCSLib.FairDivision.IsAllocationOf preferredAllocation chores ∧
                          EconCSLib.FairDivision.EFXForChores
                            (EconCSLib.FairDivision.additiveChoreCost cost) preferredAllocation ∧
                          ∀ other,
                            EconCSLib.FairDivision.additiveChoreCost cost agent
                              (preferredAllocation agent) ≤
                              EconCSLib.FairDivision.additiveChoreCost cost agent
                                (preferredAllocation other)) ∧
              (∀ dominant auxiliary : Finset (Fin 4), ∀ q : ℕ,
                dominant.card = 2 → auxiliary.card = 2 → Disjoint dominant auxiliary →
                  ∀ special ∈ auxiliary, ∀ companion ∈ auxiliary, special ≠ companion →
                    (((∀ item ∈ chores,
                      EconCSLib.FairDivision.smallAgentSet cost item = dominant) ∧
                      chores.card = 4 * q + 3) ∨
                      (∃ exceptionalItem ∈ chores,
                        EconCSLib.FairDivision.smallAgentSet cost exceptionalItem = auxiliary ∧
                        (∀ item ∈ chores.erase exceptionalItem,
                          EconCSLib.FairDivision.smallAgentSet cost item = dominant) ∧
                        (chores.erase exceptionalItem).card = 4 * q + 3)) →
                    ∃ exceptionalAllocation : EconCSLib.FairDivision.Allocation (Fin 4) Item,
                      EconCSLib.FairDivision.IsAllocationOf exceptionalAllocation chores ∧
                        EconCSLib.FairDivision.EFXForChores
                          (EconCSLib.FairDivision.additiveChoreCost cost) exceptionalAllocation ∧
                        (∀ agent, agent ≠ special → ∀ other,
                          EconCSLib.FairDivision.additiveChoreCost cost agent
                            (exceptionalAllocation agent) - 1 ≤
                            EconCSLib.FairDivision.additiveChoreCost cost agent
                              (exceptionalAllocation other)) ∧
                        (∀ item ∈ exceptionalAllocation special,
                          EconCSLib.FairDivision.IsLargeChore cost r special item) ∧
                        (∀ other, other ≠ companion →
                          EconCSLib.FairDivision.additiveChoreCost cost special
                            (exceptionalAllocation special) ≤
                            EconCSLib.FairDivision.additiveChoreCost cost special
                              (exceptionalAllocation other)) ∧
                        EconCSLib.FairDivision.additiveChoreCost cost special
                          (exceptionalAllocation special) - r ≤
                          EconCSLib.FairDivision.additiveChoreCost cost special
                            (exceptionalAllocation companion) ∧
                        (((∀ item ∈ chores,
                          EconCSLib.FairDivision.smallAgentSet cost item = dominant) ∧
                          chores.card = 4 * q + 3 ∧
                          (∀ agent, (exceptionalAllocation agent).card =
                            if agent = companion then q else q + 1)) ∨
                          (∃ exceptionalItem ∈ chores,
                            EconCSLib.FairDivision.smallAgentSet cost exceptionalItem = auxiliary ∧
                            (∀ item ∈ chores.erase exceptionalItem,
                              EconCSLib.FairDivision.smallAgentSet cost item = dominant) ∧
                            (chores.erase exceptionalItem).card = 4 * q + 3 ∧
                            exceptionalItem ∈ exceptionalAllocation companion ∧
                            (∀ agent, (exceptionalAllocation agent).card = q + 1))))


/--
Lemma (exceptional-residue combination)

Paper statement: A canonical M01 prefix extended to envy-freeness by gap filling combines with an exceptional M2 residue when both exceptional agents are long.

Source location: EFXadditivechores.tex:1709-1713
Source status: source-first audit completed

The source phrase “canonical allocation of \(M_{01}\)” is made explicit by
the `IsSmallForAtMostOne` premise: this is the defining M01 pool condition
used by the canonical `r - 1` advantage in the proof.

The source's gap-filling and residual pools are both explicitly constrained
to consist of M2 chores (small for exactly two agents); without that premise,
the stated `M2` provenance of the gap fill would be absent from the paper
claim.

This transparent proposition is the exact statement-audit target. At closeout,
its source atoms must be independently inventoried from pinned source quote
bytes and bound to this elaborated proposition rather than inferred from
identifiers.
-/
def exceptional_residue_combinationSpec : Prop :=
  by
  classical
  exact ∀ (Item : Type) (r : ℝ) (cost : EconCSLib.FairDivision.ChoreCost (Fin 4) Item) (prefixChores m2Chores gapChores residueChores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation gap : EconCSLib.FairDivision.Allocation (Fin 4) Item), 2 < r → EconCSLib.FairDivision.IsOneOrRChoreCost cost r → Disjoint prefixChores m2Chores → (∀ item ∈ m2Chores, EconCSLib.FairDivision.IsSmallForExactlyTwo cost item) → Disjoint gapChores residueChores → gapChores ∪ residueChores = m2Chores → EconCSLib.FairDivision.IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation → (∀ item ∈ prefixChores, EconCSLib.FairDivision.IsSmallForAtMostOne cost item) → (∀ agent, quota agent = a ∨ quota agent = a + 1) → EconCSLib.FairDivision.IsAllocationOf gap gapChores → (∀ agent, quota agent ≠ a → gap agent = ∅) → EconCSLib.FairDivision.EnvyFreeForChores (EconCSLib.FairDivision.additiveChoreCost cost) (fun agent => prefixAllocation agent ∪ gap agent) → ∀ exceptionalI exceptionalJ, (∃ dominant auxiliary : Finset (Fin 4), ∃ q : ℕ, dominant.card = 2 ∧ auxiliary.card = 2 ∧ Disjoint dominant auxiliary ∧ exceptionalI ∈ auxiliary ∧ exceptionalJ ∈ auxiliary ∧ (((∀ item ∈ residueChores, EconCSLib.FairDivision.smallAgentSet cost item = dominant) ∧ residueChores.card = 4 * q + 3) ∨ (∃ exceptionalItem ∈ residueChores, EconCSLib.FairDivision.smallAgentSet cost exceptionalItem = auxiliary ∧ (∀ item ∈ residueChores.erase exceptionalItem, EconCSLib.FairDivision.smallAgentSet cost item = dominant) ∧ (residueChores.erase exceptionalItem).card = 4 * q + 3))) → exceptionalI ≠ exceptionalJ → quota exceptionalI = a + 1 → quota exceptionalJ = a + 1 → ∃ allocation : EconCSLib.FairDivision.Allocation (Fin 4) Item, EconCSLib.FairDivision.IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧ EconCSLib.FairDivision.EFXForChores (EconCSLib.FairDivision.additiveChoreCost cost) allocation


/--
Appendix A proposition: no bundle contains two A items

Paper statement: In an EFX allocation of the Appendix A construction, no bundle contains two or more A items.

Source location: EFXadditivechores.tex:2074-2076
Source status: source-first audit completed

This transparent proposition is the exact statement-audit target. It is not
proof evidence; `appendix_no_two_a_items` must remain a theorem/lemma of exactly this
type and is proved by its paired theorem/lemma. At closeout, its
source atoms must be independently inventoried from pinned source quote bytes
and bound to this elaborated proposition rather than inferred from identifiers.
-/
def appendix_no_two_a_itemsSpec : Prop :=
  by
  classical
  exact ∀ (n : ℕ) (Item : Type) (r q : ℝ) (cost : EconCSLib.FairDivision.ChoreCost (Fin n) Item) (chores A B C : Finset Item) (allocation : EconCSLib.FairDivision.Allocation (Fin n) Item), 4 ≤ n → q = (2 * ((n + 1) / 2) + 1 : ℕ) + 2 → r = ((2 * ((n + 1) / 2) + 1 : ℕ) : ℝ) * (q + 1) / 2 → A.card = n - 1 → B.card = 2 * ((n + 1) / 2) + 1 → C.card = 2 * ((n + 1) / 2) + 1 → Disjoint A B → Disjoint A C → Disjoint B C → A ∪ B ∪ C = chores → (∀ (agent : Fin n) item, (item ∈ A → cost agent item = r) ∧ (item ∈ B → cost agent item = if agent.val < n / 2 then 1 else q) ∧ (item ∈ C → cost agent item = if agent.val < n / 2 then q else 1)) → EconCSLib.FairDivision.IsAllocationOf allocation chores → EconCSLib.FairDivision.EFXForChores (EconCSLib.FairDivision.additiveChoreCost cost) allocation → ∀ (agent : Fin n), (allocation agent ∩ A).card ≤ 1


/--
Appendix A proposition: p1 and p2 lower bounds

Paper statement: In an EFX allocation of the Appendix A construction, the two groupwise minimum bundle costs p1 and p2 are each at least r.

Source location: EFXadditivechores.tex:2104-2106
Source status: source-first audit completed

This transparent proposition is the exact statement-audit target. It is not
proof evidence; `appendix_p1_p2_lower_bounds` must remain a theorem/lemma of exactly this
type and is proved by its paired theorem/lemma. At closeout, its
source atoms must be independently inventoried from pinned source quote bytes
and bound to this elaborated proposition rather than inferred from identifiers.
-/
def appendix_p1_p2_lower_boundsSpec : Prop :=
  by
  classical
  exact ∀ (n : ℕ) (Item : Type) (r q : ℝ) (cost : EconCSLib.FairDivision.ChoreCost (Fin n) Item) (chores A B C : Finset Item) (allocation : EconCSLib.FairDivision.Allocation (Fin n) Item) (P1 P2 : EconCSLib.FairDivision.Bundle Item → ℝ) (p1 p2 : ℝ), 4 ≤ n → q = (2 * ((n + 1) / 2) + 1 : ℕ) + 2 → r = ((2 * ((n + 1) / 2) + 1 : ℕ) : ℝ) * (q + 1) / 2 → A.card = n - 1 → B.card = 2 * ((n + 1) / 2) + 1 → C.card = 2 * ((n + 1) / 2) + 1 → Disjoint A B → Disjoint A C → Disjoint B C → A ∪ B ∪ C = chores → (∀ (agent : Fin n) item, (item ∈ A → cost agent item = r) ∧ (item ∈ B → cost agent item = if agent.val < n / 2 then 1 else q) ∧ (item ∈ C → cost agent item = if agent.val < n / 2 then q else 1)) → EconCSLib.FairDivision.IsAllocationOf allocation chores → EconCSLib.FairDivision.EFXForChores (EconCSLib.FairDivision.additiveChoreCost cost) allocation → (∀ bundle, P1 bundle = r * (bundle ∩ A).card + (bundle ∩ B).card + q * (bundle ∩ C).card) → (∀ bundle, P2 bundle = r * (bundle ∩ A).card + q * (bundle ∩ B).card + (bundle ∩ C).card) → (∀ (agent : Fin n), agent.val < n / 2 → EconCSLib.FairDivision.additiveChoreCost cost agent = P1) → (∀ (agent : Fin n), n / 2 ≤ agent.val → EconCSLib.FairDivision.additiveChoreCost cost agent = P2) → (∃ agent, P1 (allocation agent) = p1) → (∀ agent, p1 ≤ P1 (allocation agent)) → (∃ agent, P2 (allocation agent) = p2) → (∀ agent, p2 ≤ P2 (allocation agent)) → p1 ≥ r ∧ p2 ≥ r


end HT26EFXChores
