---
name: econcs-prover
description: Prove or repair Lean theorems in EconCSLib. Use when asked to close sorry/admit gaps, fix failing theorem proofs, repair broken Lean files after API or statement changes, derive paper-facing results from existing paper assumptions, or run compiler-guided proof search for EconCSLib paper or shared-library lemmas. Focuses on proof construction, tactic/API search, source-faithful theorem repair, and targeted Lean validation.
---

# EconCS Prover

This is the proof-production skill for EconCSLib. Use it after the paper
statement target is known, or when an existing theorem proof fails and needs to
be repaired.

This skill complements the workflow skills:

- Use `skills/econcs-formalizer/SKILL.md` for paper setup, source inventory,
  paper interface rules, public/private sync, and closeout validation.
- Use `skills/econcs-formalizer/references/proof-strategies.md` to route into
  the smallest relevant domain proof reference.
- Use `skills/lean-community-conventions/SKILL.md` for new shared-library APIs,
  naming, style, and proof-claim gates.
- Read `references/proving-workflow-provenance.md` when updating this skill,
  explaining its literature provenance, or citing why the workflow is designed
  this way.

## Proof Loop

### 1. Fix the Target

Start from the exact theorem, not the surrounding paper:

1. Identify the failing declaration, file, and intended source statement.
2. Run the narrowest Lean command that checks the declaration or file.
3. Record the first real error and current goal shape before editing.
4. Confirm whether the theorem statement should be fixed or the proof should be
   repaired.

Do not weaken a paper-facing theorem silently. If the source statement is
conditional, expose the source condition. If the source is false or
underspecified, stop treating the issue as proof search and write a source note
or corrected conditional theorem.

Useful commands:

```bash
lake env lean papers/<Paper>/<File>.lean
lake build <known-module-or-target>
rg -n "theorem_name|key_definition|source_phrase" EconCSLib papers Mathlib Cslib
rg -n "sorry|admit|axiom" papers/<Paper> EconCSLib
```

### 2. Retrieve Before Inventing

Before writing a new definition or long helper proof, search existing APIs:

- Search local paper files for already-proved source steps.
- Search `EconCSLib/` for reusable math, probability, optimization, matching,
  social-choice, auction, and graph lemmas.
- Search `Mathlib/`, `Cslib/`, and `Optlib/` if they are present in the Lake
  dependency tree.
- Check potential upstream Lean sources listed in
  `docs/UPSTREAM_LEAN_SOURCES.md` before porting EC/game-theory/social-choice
  infrastructure.

If you use or port material from an upstream Lean source, cite the repository
URL, file/module path, commit or release when available, license status, and
the local adaptation in the paper-local report or library docstring. Do not
copy code from an upstream source without preserving provenance.

### 3. Decompose the Goal

Use the source proof and Lean goal state together:

- State the top-level proof route in one or two concrete obligations.
- Prove helper lemmas only when they discharge repeated or conceptually named
  obligations.
- Keep helper statements stronger only when the stronger form is reusable or
  materially simplifies the proof.
- Prefer source-shaped paper-local wrappers over opaque certificate records.
- Move a helper into `EconCSLib/` only if it is genuinely reusable outside the
  current paper.
- If a conjecture, stronger theorem, or extension looks trivial, leave it until
  the source theorem chain is stable. Then either prove it as explicitly
  beyond-paper material or record it for the final extension pass; do not count
  it as paper coverage.

The best proof route is usually source-faithful, but source fidelity is not a
requirement to mimic every informal sentence. A proof-route deviation is a
substantive change in mathematical approach; record both the original source
route and the Lean route. Missing assumptions, explicit source hypotheses, and
interface notes belong in assumption/status notes, not in proof deviations.

### 4. Run Compiler-Guided Repair

Treat Lean as the verifier and the error message as the next proof-state query:

1. Make one local proof change.
2. Re-run the narrow check.
3. Inspect the new first error or goal.
4. Search or derive the missing premise.
5. Keep the successful fragment and delete exploratory commands.

Use tactic suggestions as hints, not final opaque output:

```lean
  exact?
  apply?
  rw?
  simp?
  aesop?
```

After a suggestion works, simplify it into a readable proof when possible. Do
not leave diagnostic `#check`, `#print`, `set_option pp.all true`, or tactic
probe blocks in committed code unless they are intentionally documented tests.

### 5. Classify Failures

When proof search loops, classify the obstruction before continuing:

- **API drift:** theorem or field names changed; repair imports or names.
- **Typeclass/instance gap:** add the missing local instance, `classical`, or
  explicit finite/decidable hypothesis.
- **Hypothesis mismatch:** prove a bridge lemma from existing assumptions
  instead of changing the theorem.
- **Side condition:** isolate nonzero, positivity, finite-support,
  measurability, integrability, or boundedness obligations.
- **Wrong formal target:** the Lean statement does not match the paper claim;
  repair the statement and restart validation for that row.
- **Missing library theorem:** prove the reusable theorem, use an approved
  external boundary, or mark the paper partial. Do not replace it with a broad
  assumption bundle.

## Common Proof Moves

Use these as first-pass tactics before broader redesign.

### Algebra, Order, and Arithmetic

- Normalize expressions with `ring_nf`, `norm_num`, `simp`, or `field_simp`
  only after side conditions are explicit.
- Use `linarith` for linear inequalities and `nlinarith` for polynomial
  inequalities after rewriting hypotheses into the same variables.
- Prove denominators/nonzero conditions early; many EconCS proofs hide them in
  model assumptions.
- For strict inequalities, check whether the source has an interior condition
  such as `0 < p` and `p < 1`; if so, expose it as an assumption rather than a
  caveat.

### Finite Sets, Lists, and Counting

- Start with extensionality and membership normal forms:
  `ext x`, `simp [Finset.mem_filter]`, `by_cases h : x = y`.
- Keep `DecidableEq`, `Fintype`, nonempty, and finiteness assumptions visible.
- For sums/products, reduce to pointwise equalities before invoking `simp`,
  `sum_congr`, or induction.

### Probability, Measure, and Analysis

- Decide whether the source claim is pointwise or almost-everywhere. Many
  continuous EconCS arguments are naturally `ae` statements.
- Separate measurability, integrability, nonnegativity, and finiteness before
  proving the main inequality or convergence claim.
- Prefer reusable probability lemmas for expectation, variance, distributions,
  CTMCs, and renewal/reward arguments over paper-local re-encodings.

### Optimization and Certificates

- Separate feasibility, objective comparison, optimality, uniqueness, and
  certificate soundness into distinct lemmas.
- Do not let an `isMax`, `isOptimal`, `certificate`, `bridge`, or `replay`
  field be the whole proof unless another checked row derives that field from
  source primitives.
- For LP and finite optimization, prove the finite/candidate reduction first,
  then prove the chosen candidate's objective inequality.

### Mechanisms, Matching, and Social Choice

- Reuse executable semantics for auctions, matching, STV/RCV, rankings, and
  choice functions when available.
- Keep tie-breaking, strictness, support, and feasibility assumptions explicit.
- Prove equivalence to the paper's algorithmic step before proving downstream
  welfare, stability, monotonicity, or strategyproofness claims.

## Repair Guardrails

- Do not leave `sorry`, `admit`, `by omega?`-style failed fragments, temporary
  `axiom`s, or broad theorem-shaped assumptions in final code.
- Do not make a paper `formalized` by assuming an intermediate theorem that the
  paper expects to prove.
- Do not hide theorem-level conditions inside opaque records merely to shorten
  a paper-facing statement.
- Do not update DAGs, validation reports, dashboards, or website metadata
  during ordinary proof loops unless the user asked for closeout or a real
  proof boundary has been reached.
- Do not edit protected human prose such as the repository README or
  human-written summaries unless the user explicitly asks for that text change.

## Validation Boundary

After closing or repairing a theorem:

1. Run the targeted Lean check for the edited file.
2. Run the narrowest relevant module or paper build if imports changed.
3. Scan the touched files for `sorry`, `admit`, and temporary `axiom`.
4. Inspect the diff for accidental statement weakening or unrelated churn.
5. If the proof changes a paper-facing statement or assumption, update only the
   required source-facing artifacts and defer full closeout unless requested.

At closeout, hand off to
`skills/econcs-formalizer/references/post-formalization-closeout.md`; this
skill stops at proof repair and Lean validation.
