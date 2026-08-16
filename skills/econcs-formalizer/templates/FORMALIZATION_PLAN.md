# Formalization Plan: {{TITLE}}

This is the paper-local outside-Lean scratchpad. Keep it short enough to guide
proof work, but complete enough that another agent can see the theorem target,
source risks, and reusable-library choices before opening Lean files.

- Namespace: `{{NAMESPACE}}`

## Initial Outside-Lean Paper Audit

- Source version / local files inspected:
  - Official source:
  - Open/source-of-truth version:
  - Local PDF/TeX/text caches:
  - Canonical auditable text/TeX artifact and SHA-256:
  - Provenance PDF/archive and SHA-256, if distinct:
  - Locator scheme (page/section/theorem/equation or TeX file/line):
  - Extraction notes:
- Audit mode:
  - `named_theoretical_statements` (default) or
    `deep_paper_with_all_prose_claims` (explicitly requested):
  - Why any deep-paper mode is required:
- Independent source-only named-presentation receipt:
  - `source_named_result_inventory_review` schema / receipt path / artifact
    path / artifact SHA-256 / index digest:
  - `complete: true`, validator, method, timestamp, and source/index pins:
  - Source environments and visible headings searched:
  - Declarative custom environment/heading-to-kind mappings:
  - Complete byte-pinned `prose_definition_presentations` ledger and digest
    (write an explicit empty list when none are found):
  - Source-only disposition for every prose definition: normal named theory,
    repeated normal presentation, local proof notation, computational, or
    deep-only; content-pinned independent scope judgment for every exclusion
    and explicit approval for any catch-all deep-only disposition:
  - Canonical normal-definition statement digest and independently reviewed
    semantic-equivalence receipt; repeated-presentation semantic aliases:
  - Unclassified named presentations and resolution:
  - Named open problems and explicit source-declared-open nonproof disposition
    (`source_kind: "open_problem"`, `claim_bearing: false`,
    `source_scope_classification: "source_declared_open_nonresult_observation"`,
    `coverage_status`/`protocol_role: "source_declared_open"`):
- Source/version mismatch notes:
  - Publication/source-version differences:
  - Theorem-level differences found:
- Complete named-result ledger status:
  - Source files searched:
  - Named or source-presented definitions, theoretical results, assumptions,
    model conditions, and named appendix theory extracted:
  - Unlabelled conditions retained only because they are dependencies of a
    selected item:
  - Standalone formulas, equations, algorithms, and computational/complexity
    claims retained for deep audit or selected-result dependencies only:
- Formula sanity check:
  - Signs/constants/domains:
  - Density vs mass / likelihood-kernel representation issues:
  - Dependency map between named source results:
  - Selected named/visibly numbered formula or equation claims that need
    derivation, not source-row assumptions:
- Named result sanity check:
  - Results that look correct as stated:
  - Suspected bugs, missing assumptions, or ambiguous wording:
- Initial generalization / conjecture / extension scan:
  - Assumptions that seem trivially weakenable or removable:
  - Stronger conclusions or corollaries that appear immediate from the source
    proof route:
  - Natural conjectures or extensions that look trivial, nontrivial, or false:
  - Extension targets to try only after the paper's source claims are closed:
- Shared-library reuse checkpoint:
  - Mathlib declarations/modules inspected:
  - Cslib declarations/modules inspected:
  - Optlib declarations/modules inspected:
  - Other potential upstream sources inspected:
  - Upstream sources used or ported, with citation/provenance:
  - Existing `EconCSLib` declarations/modules inspected:
  - API chosen and near-misses:
  - Source-defined objects that will use reusable library definitions, and the
    planned paper-local semantic bridge/equivalence rows:
    - Each bridge row must be listed on the configured review or assumption
      surface, carry a `Source status:` comment, and be referenced from
      `audit/paper_statement_map.json` under a semantic/equivalence bridge
      field. Matching the source object by Lean/library/source name alone is
      not source evidence.
- Proof strategy consequences:
  - Source proof route to follow:
  - Cleaner Lean route or reusable library route:
  - Major issues already reported to the user:

## Source Inventory

- Source semantic identity / byte-pinned locator / compact source evidence for
  every selected item:
- Named or visibly numbered definitions, results, claims, formulas, equations,
  algorithms, assumptions, model conditions, and named appendix items:
- Unlabelled conditions included as selected-item dependencies:
- Named open problems with source-declared-open nonproof disposition:
- Custom presentation mappings and any source-presentation classification
  decisions:
- `deep_paper_with_all_prose_claims` material, only when that mode was
  explicitly requested: prose claims, figures, tables, captions, numerical
  examples, simulations, empirical material, and other nonselected content.
- Do not treat source-map keys, aliases, Lean declaration names, or matching
  terminology as coverage evidence.

## Initial Proof Strategy

After the source receipt, selected item/dependency map, audited interface
skeleton, and next proof seam are recorded, prioritize proof work. Update this
plan or other documentation only at a material boundary: changed source scope,
new or resolved obligation, status change, or closeout.

- Main theorem chain:
- Likely reusable `EconCSLib` seams:
- Paper steps that look underspecified or analytically hard:
- Trivial generalization/conjecture/extension targets to revisit after the
  source theorem chain is stable:
- Formal target map:
  - Rows to fully prove now:
  - Deep-mode-only nonformal rows, when explicitly requested, with source-based
    classification and coverage evidence:
  - Explicit assumption/certificate boundaries, if any:
- Planned fallback route if the source proof is too informal:

## Reusable-Library TODO

- Library APIs to use directly:
- Small reusable lemmas to add now:
- Larger reusable components to defer:
- Library-audit risks:

## Audited Statement Skeleton

Before proof work, write every selected paper-facing formal item with its
complete source-shaped Lean type and a temporary private `by sorry` proof body.
Run the current semantic statement and recursive premise-provenance audits, then
freeze the canonical elaborated-signature manifest here. A theorem name is only
a navigation key; the elaborated type is the reviewed object.

For each row, enumerate source and Lean obligations and review every semantic
dimension triggered by the actual statements: quantifiers and domains, numeric
representation and boundary behavior, data/container/order semantics,
algorithmic input/output/stopping behavior, and advertised complexity where
present. For probability or measure-theoretic rows, also record the law,
conditioning convention, definedness conditions, and any parameter or
transformation bridge that the statements actually use. For finite or strict
claims, record the applicable cardinality threshold and witness/boundary
evidence. Do not apply a fixed domain-specific checklist to a row whose source
and Lean semantics do not trigger it.

Every claimed correspondence needs an explicit Lean equality, iff, theorem, or
proof route bound to the reviewed obligations. A wrapper, a familiar term, a
finite calculation, or a declaration/function name is not semantic evidence.
Names are navigation only.

### Source Route Discipline

For every `source_routes` entry, record the canonical source item, current
source-semantic digest, exact locator, unique current fully elaborated Lean
signature/dependency identity, route kind, and semantic scope/evidence.
Use `direct` only when the row is an exact equivalent paper-facing endpoint
with an exact source-conclusion/Lean-conclusion equivalence. In a composite
row, pin every scoped source component separately as `source_component`; it
needs a Lean conclusion and substantive scope/evidence, not a fabricated full
theorem equivalence. `source_model_convention` is only for an explicit source
model reading; `defect_or_remark_support` is only for quarantined/support-only
material; and `proof_support` needs a substantive source-support scope and
never gives endpoint credit. Declaration and function names are navigation
only.

Before full closeout, retain the current protocol-required source-record and
semantic-model judgments for every row whose expanded semantics trigger them.
Each generated judgment key must be nonempty, unique, and tied to the exact
source item and elaborated signature. A live source defect, unresolved semantic
dimension, added non-source premise, or weakened conclusion is not repaired by
renaming a parameter or route; record it as the appropriate open obligation or
status boundary.

| Source semantic item / exact locator | Lean navigation key (not evidence) | Current elaborated signature/dependency identity | Statement verdict | Premise provenance | Proof body |
|---|---|---|---|---|---|
| | | | pending | pending | `by sorry` |

Any signature change after review makes the row stale and requires re-audit.
Replacing `sorry` with a proof while preserving the type does not.

## Execution Checklist

- [ ] Create a canonical text/TeX source artifact, provenance record, and
      independent source-only named-presentation receipt pinned by SHA-256.
- [ ] Classify every named presentation declaratively; resolve unclassified
      presentations and record named open problems as explicit nonproof items.
- [ ] Complete the selected normal-mode inventory: named/visibly numbered
      definitions, results, claims, formulas, equations, algorithms,
      assumptions, model conditions, named appendix items, and their unlabelled
      dependencies. Enter deep mode only on an explicit request.
- [ ] Pin each selected item and theorem premise by source semantic identity,
      byte locator, and compact source evidence.
- [ ] After a source-map change, run `--source-inventory-check`. Reuse only an
      unchanged item whose current source-semantic digest schema/digest and
      unique current elaborated Lean signature/dependency identity agree. Normal
      checks write nothing;
      explicitly refresh only affected items after the source map, interface,
      and status surface are stable. Revalidate byte anchors when artifact bytes
      change, and fail closed on missing pins or ambiguity.
- [ ] Defer exploratory generalizations, conjectures, and extensions until the
      selected source proof chain is stable.
- [ ] Fill the formal target map and declare any intended boundary/certificate.
- [ ] For each statement-match row, enumerate source/Lean assumption and
      conclusion atoms, exact source locators, explicit mathematical bridge
      statements, and exact unmatched/unjustified obligation-id lists. Do not
      classify a weakened source conclusion as a conditional boundary.
- [ ] Build or select reusable library APIs before adding paper-local wrappers.
- [ ] Replace the paper scaffold with all source-facing Lean definitions and
      exact theorem types, using `by sorry` only as the temporary private proof
      body for each statement row.
- [ ] Run the current statement and source-record/provenance checks on the
      complete skeleton; freeze every elaborated signature/dependency identity.
- [ ] Complete every semantic review dimension triggered by the source and Lean
      statements. Do not mark a dimension absent merely because a wrapper,
      source phrase, or declaration name appears familiar.
- [ ] Prove all rows marked in-scope, or downgrade them with an explicit
      boundary note.
- [ ] Replace every skeleton `sorry` without changing the audited type; rerun
      statement review if a type changes.
- [ ] At closeout, update README, status, DAG, and validation report from the
      same row list.
- [ ] At closeout, run the targeted paper build, audits,
      placeholder/provenance checks, and DAG validation.
- [ ] Record any unresolved source bug, assumption, or library debt.

## Active Scratchpad

- Current Lean endpoint:
- Exact current mathematical gap:
- Next bridge lemmas to try:
- Informal proof sketch / recurrence / construction:

## Deviations And Assumptions

- Source imprecision or substantive proof-route deviation to report later
  (source route vs Lean route):
- Genuine paper assumptions to declare in `Assumptions.lean`:
- Temporary certificate fields to discharge:
- Validation/audit checks that must inspect these assumptions:
  coverage, LLM-as-judge, source-record, holistic source-first, DAG/source-json:
