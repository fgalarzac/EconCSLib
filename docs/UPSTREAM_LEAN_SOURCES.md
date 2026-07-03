# Potential Upstream Lean Sources

This note records Lean repositories that agents may scout before creating new
`EconCSLib` APIs. Not every source listed here is a dependency. Treat these as
places to inspect for definitions, theorem shapes, proof patterns, and possible
small imports; only add a Lake dependency after checking toolchain
compatibility, license fit, API stability, and user approval.

If an agent uses or ports material from any upstream source, cite it. This
includes copied or translated definitions, theorem statements, proof structure,
module organization, or nontrivial proof ideas. Record the repository URL,
file/module path, commit or release when available, license status, and what
was reused. Put this provenance near the resulting Lean code or in the relevant
paper/formalization plan; also add a bibliography or documentation citation
when the reuse affects human-facing paper text.

## Current Imported Sources

- Mathlib: the main mathematical upstream. Search it first for standard
  structures, algebra, order, topology, probability, measure, optimization, and
  analysis facts.
- CSLib: the current computer-science upstream dependency. See
  [`CSLIB_COMPATIBILITY_NOTES.md`](CSLIB_COMPATIBILITY_NOTES.md) for pinned
  version, import boundaries, and known useful modules.
- Optlib: scout when it exists in the workspace or Lake manifest for
  optimization-specific APIs.

## Potential Additional Sources

- <https://github.com/elazarg/GameTheory>: candidate source for game-theory
  definitions, equilibrium-style theorem statements, and proof organization.
- <https://github.com/alexfleetcommander/lean-proofs>: candidate source for
  Lean proof examples and reusable proof patterns.
- <https://github.com/gametheoryinlean/EconCSLib>: independent Economics and
  Computation concept-library project. Scout it for domain models, notation,
  theorem organization, and APIs that may overlap with this repository.

## Agent Workflow

Before creating a paper-local wrapper or reusable `EconCSLib/` primitive for a
common proof seam:

1. Search Mathlib, CSLib, Optlib when present, and existing `EconCSLib/`
   modules.
2. For overlapping game-theory, EC, social-choice, mechanism-design,
   optimization, or proof-pattern seams, also scout the potential additional
   sources above.
3. Record inspected modules, APIs chosen, near misses, and citation/provenance
   for any material used or ported in the paper's formalization plan.
4. Prefer thin bridge lemmas around existing upstream APIs when they fit. If an
   upstream source almost fits but cannot be used directly, record why before
   adding a local primitive.
