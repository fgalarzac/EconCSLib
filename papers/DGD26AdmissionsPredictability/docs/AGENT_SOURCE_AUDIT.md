# Agent Source Audit: DGD26AdmissionsPredictability

## Overall status: PASS

Audit standard: I checked the source inventory from the source itself, then inspected the Lean interface for omissions, hidden strengthening/weakening, and semantic mismatches.

This is an independent source-first holistic audit of the current public
DGD26AdmissionsPredictability formalization. I read the official arXiv-rendered
source text for the paper, checked the source inventory from the source itself,
and compared its definitions, main theoretical statements, and appendix theorem
inventory against the curated source map, `PaperInterface.lean`, and the current
audit sidecars. This audit uses the sidecars as evidence, but it does not merely
summarize existing sidecars; it checks for omissions, hidden
strengthening/weakening, and semantic mismatches.

## Source Inventory

The source-facing mathematical inventory consists of the finite choice-function
model and the paper's theoretical claims:

- Definitions of choice functions, q-acceptance, total-order queues, choice
  distance, d-instability, tight d-instability, substitutability, variability,
  monotonicity, consistency, independence, q-representativeness, sequential
  composition, borderline/waitlisted sets, and linear-assignment induced choice.
- Main-text representation and characterization results: independent ML rules
  only represent 0-unstable rules, rank-threshold rules represent the
  one-variable/one-unstable case, q-representative rules are characterized by
  q-acceptance plus 1-instability and variability at most one, and
  q-acceptant choice functions are nonzero-unstable under nontrivial capacity
  conditions.
- Appendix results: substitutability equivalent to 1-instability under
  q-acceptance, the 2q instability bound and tight even/odd examples,
  sequential composition preserving substitutability and giving additive
  variability bounds, and the LAP ordering/instability/variability statements.
- Source-quality note: the curated inventory records the corrected removable
  sets lemma, where the TeX source repeats `V_C(X1)` on both sides.

The public repo does not track the source TeX/PDF. The paper-local source map
records the source locations from the arXiv TeX/formula source and the AAAI
publication metadata.

## Lean Interface Comparison

`PaperInterface.lean` exposes the paper in the same conceptual order: source
definitions first, then ML representation and instability/variability
statements, then appendix structural lemmas, sequential composition, and the
LAP results. The main statements are not hidden behind a single broad theorem:
the interface decomposes the paper into 66 reviewed source rows and related
definition rows, with auxiliary proof-facing rows kept out of the human review
surface.

The source-to-interface comparison did not identify a missing main-text
definition, proposition, theorem, or appendix theorem from the curated source
inventory. The exact-variability row visibly carries the nondegenerate
displacement witness needed to distinguish "exactly one" from "at most one";
that is now the only source-record boundary input, and it is recorded as a
source-level exactness condition rather than as hidden proof machinery.

## Machine Audit Results

- Source-to-dashboard coverage: 39/39 source statements covered directly.
- Row-local statement matching: 66 current reviewed rows, 101 current
  statement-judge rows, no stale or flagged items.
- Assumption/source-condition provenance: 0 explicit assumption declarations.
- Source-record audit: 1 visible boundary input, the displacement witness for
  exact variability one; the current source-record judge is tied to the
  regenerated audit digest.
- Lean build target: `lake build DGD26AdmissionsPredictability`.

## Findings

No unresolved paper-facing proof gap is recorded for the curated mathematical
source inventory. The empirical NYC application claims are outside the Lean
theorem target and are correctly treated as descriptive rather than formalized
mathematical theorems.

## Why This Audit Exists

The structured LLM-as-judge lanes are row-local. This artifact records a
separate source-inventory-to-interface pass so future agents must start from
the paper's mathematical claims rather than from the rows that already happen
to be exposed.
