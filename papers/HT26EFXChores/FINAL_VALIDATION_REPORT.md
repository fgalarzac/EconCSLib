# Final Validation Report: EFX for Additive Chores

Updated: 2026-08-18

## 1. Human Verdict

The paper's named theoretical surface is formalized. The checked surface
includes the displayed fairness and allocation definitions, Theorems 1--3,
their named supporting propositions and lemmas, and the two named Appendix A
propositions. Independent reviewer annotations may be added through the packet
or dashboard, but are not a prerequisite for this formalization status.

## 2. Closeout Status

- Completion status: formalized.
- 22 source claims are in scope: six definitions, three theorems, six
  propositions, and seven lemmas.
- Every selected claim has a direct paper-facing semantic statement and a
  checked proof route. No theorem-level boundary remains within this scope.

## 3. Source and Scope

- Paper: Wentao He and Biaoshuai Tao, *EFX for Additive Chores:
  Nonexistence, Pareto Incompatibility, and Bi-Valued Existence*.
- Source version: [arXiv v2 (2026-07-09)](https://arxiv.org/abs/2606.08872v2).
- Formalized paper surface: the definitions of EF for chores, EFX for chores,
  Pareto-optimality, canonical allocation, canonical short/long labels, and
  super-canonical allocation; Theorems 1--3; the named propositions and
  lemmas supporting those results; and the named Appendix A propositions.
- Scope boundary: remarks, literature comparisons, and external-algorithm
  discussion are not named theoretical claims in this review surface.

## 4. Researcher Summary of Checked Results

- **Theorem 1 (tri-valued EFX nonexistence).** For every \(n \geq 4\), there
  is a tri-valued instance with \(n\) agents that has no EFX allocation. The
  formalized route includes the four-agent construction and the Appendix A
  extension to arbitrary \(n\).
- **Theorem 2 (EFX and Pareto-optimality incompatibility).** For every
  \(n \geq 4\) and \(r > \lceil n/2 \rceil + 1\), there is a
  \((1,r)\)-bi-valued instance with \(n\) agents in which every EFX allocation
  is not Pareto-optimal. The checked supporting propositions establish the
  required large-item and cost lower bounds before the Pareto comparison.
- **Theorem 3 (four-agent bi-valued EFX existence).** Every four-agent
  bi-valued instance has an EFX allocation. The checked route covers the
  paper's M01/M2/M34 decomposition, the low- and high-ratio cases, balanced
  orientations, insertion, composition, and the exceptional residue case.

## 5. Remaining Boundaries and Gaps

None within the selected named theoretical surface.

## 6. Additional Assumptions Beyond Paper

None. Finiteness, additivity, the number of agents, the cost-ratio bounds, and
the construction-specific conditions used by the results are stated source
conditions, not added assumptions.

## 7. Proof-Strategy Deviations

None. The formal proof routes retain the paper's construction-based split:
the tri-valued construction and its appendix extension for Theorem 1, the
A/B/C construction and EFX lower bounds for Theorem 2, and the M01/M2/M34
case analysis for Theorem 3.

## 8. Proof Structure Worth Reusing

Theorem 3 provides a useful finite-allocation pattern. First partition items
by their role in the instance, establish an EFX allocation for the central M2
piece, orient the remaining small-item structure in a balanced way, and then
insert or compose the M34 residue while preserving the relevant inequalities.
Theorem 2 illustrates the complementary obstruction pattern: derive
allocation-wide lower bounds from EFX, then exhibit a Pareto improvement that
the lower bounds rule out for an EFX allocation.

## 9. Generalizations, Conjectures, and Extensions

This closeout makes no existence claim for more than four agents beyond the
results stated in the source. Theorem 1 and Theorem 2 already quantify over
arbitrary \(n \geq 4\); Theorem 3 is deliberately reported only in its stated
four-agent form.

## 10. Source Clarifications and Exact Readings

None identified in the audited source version.

## 11. Paper Issues or Caveats

None within the reviewed named theoretical surface.

## 12. Checked Claim Inventory

The 22 checked source claims are organized as follows:

- **Model and allocation vocabulary:** the displayed definitions of EF for
  chores, EFX for chores, Pareto-optimality, canonical allocation, canonical
  short/long labels, and super-canonical allocation.
- **Theorem 1 route:** Theorem 1, the four-agent proposition that no bundle
  has two A items, the proposition that an A-free bundle is expensive, and the
  two Appendix A propositions used in the arbitrary-agent extension.
- **Theorem 2 route:** Theorem 2, the proposition that every EFX agent receives
  a large item, and the EFX cost-lower-bound proposition.
- **Theorem 3 route:** Theorem 3; the M34 insertion, composition, canonical
  allocation properties, balanced orientation, M2 EFX allocation, M2 EFX
  allocation properties, and exceptional-residue-combination lemmas.

The [human review packet](docs/HUMAN_REVIEW_PACKET.pdf) presents these claims
in dependency order with the corresponding source inputs and reviewer
annotation space. The interactive dashboard, launched with
`papers/HT26EFXChores/review-dashboard.sh`, is an optional alternative to
using the PDF.

## 13. Source and Assumption Provenance

Each of the 22 claims is anchored to the selected arXiv TeX source and its
local location is recorded in the [statement map](audit/paper_statement_map.json).
The theorem summaries above use the theorem statements at lines 304--306,
416--418, and 532--534 of that source. The map also records the source anchors
for every supporting proposition and lemma rather than treating their proof
use as implicit.

## 14. Semantic Review and Proof Evidence

For each selected source claim, the [raw source-to-specification ledger](audit/v11_raw_source_spec_screening.json)
records the direct comparison between the byte-pinned source input and its one
semantic review target. The paired Lean theorem is separately checked as the
proof endpoint for that target. The [current focused-build receipt](audit/FOCUSED_BUILD_RECEIPT.json)
and [final closure receipt](FINAL_CLOSURE_RECEIPT.md) identify the current
validation run.

## 15. Reused Definitions

Reusable allocation and chore-fairness vocabulary is reviewed under the same
source-to-semantics standard as paper-local code. The [library review ledger](audit/library_semantic_review.json)
records the direct source connection for the finite-allocation, cost, EF, EFX,
and Pareto prerequisites used by the paper claims. They are review inputs, not
extra claims attributed to this paper.

## 16. Dependency DAG

The [dependency DAG](docs/DependencyDAG.pdf) separates the shared definitions
from the Theorem 1, Theorem 2, and Theorem 3 routes, and places the supporting
propositions and lemmas before the results that use them. It is a companion to
the claim inventory, not a replacement for the source comparisons above.

## 17. Validation Materials

- [Human review packet (PDF)](docs/HUMAN_REVIEW_PACKET.pdf)
- [Dependency DAG (PDF)](docs/DependencyDAG.pdf)
- [Statement map](audit/paper_statement_map.json)
- [Source-to-specification ledger](audit/v11_raw_source_spec_screening.json)
- [Library review ledger](audit/library_semantic_review.json)
- [Final closure receipt](FINAL_CLOSURE_RECEIPT.md)
