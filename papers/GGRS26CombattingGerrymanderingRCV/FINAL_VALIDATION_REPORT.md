# Final Validation Report: GGRS26 Combatting Gerrymandering with Ranked Choice Voting

Updated: 2026-07-31

## 1. Human Verdict

Formalized for the normal source-only named-theory scope. The pinned paper has
two distinct named mathematical results, Lemma C.1 and Proposition 1, and both
have direct Lean proofs with source-equivalent paper-facing statements.
Independent human review has not been recorded.

## 2. Closeout Status

- Completion status: formalized.
- Normal scope: Lemma C.1 and Proposition 1.
- Results: the PAV selector and the two-party STV/PAV rounded seat-share result
  cover all legal ballot-routed transfer choices.
- One-sentence recap: the PAV selector lemma and the two-party STV/PAV rounded
  seat-share proposition are proved for the source model, including all legal
  ballot-routed surplus transfers and a nonempty execution domain.
- Review packet: [human review packet](docs/HUMAN_REVIEW_PACKET.pdf) presents
  the source excerpts, semantic Lean targets, supporting library definitions,
  and reviewer annotations in claim-dependency order.
- Human review: independent sign-off has not yet been recorded.
- No named-theory proof obligation remains open.

## 3. Source and Scope

- Paper: *Combatting Gerrymandering with Ranked Choice Voting: an Experimental
  Analysis of Multi-member Districts in the United States*.
- Public source: [Operations Research](https://doi.org/10.1287/opre.2024.1167).
- Audited source: `cited publication`, SHA256
  `57762234dc7b4a41d10b7f05110551853ab717136eca7b9216da9425cfb8bce5`.
- Source inventory: `audit/paper_statement_map.json`.
- Human-facing Lean surface: `PaperInterface.lean`.

Normal named-theory scope contains Lemma C.1 and Proposition 1. The appendix
repeats Proposition 1, but that repetition is a pinned presentation alias, not
a third theorem. Empirical redistricting data, map-generation implementation,
simulation estimates, figures, and runtime discussion are outside this scope.

## 4. Researcher Summary of Checked Results

Lemma C.1 constructs the finite leftmost PAV maximizer and proves that it is the
unique integer in the paper's half-open interval.

Proposition 1 starts from a finite two-party electorate with solid-coalition
ballots and an operational ballot-routed STV transfer policy. Every legal
terminal execution gives a Republican seat count in
`{floor (y_R M), ceil (y_R M)}`, and the selected PAV outcome obeys the same
bound. The proof covers all legal minimum-tally and transfer choices, so the
paper's D-favoring tie convention is included. A companion theorem constructs
a legal terminal execution from the same initial state, ruling out a vacuous
universal claim.

## 5. Remaining Boundaries and Gaps

None for named theory. The unnumbered map-generation and runtime prose would
require a separate deep computational audit and receives no theorem credit in
this closeout.

## 6. Additional Assumptions Beyond Paper

None. The two explicit model conventions are source conditions rather than new
assumptions: Lemma C.1 uses `0 < y_R <= 1`, and Proposition 1 uses a genuinely
two-party active-candidate universe. Both are visible in the reviewed route.

## 7. Proof-Strategy Deviations

The Lean proof replaces the appendix's temporary turnout-divisibility
simplification with exact floor-Droop arithmetic for every stated integer
turnout satisfying `V >= M (M + 1)`. It also proves the result for every legal
ballot-routed surplus transfer rather than choosing one transfer execution.
The older raw-run refinement route remains compatibility support and receives
no source credit.

## 8. Proof Tricks Worth Reusing

- State transfer semantics on actual ballot weights: a quota election removes
  exactly one quota from the winner's support, preserves off-support weights,
  and never increases retained supporting weight.
- Audit a universal execution theorem together with a separately proved
  nonempty execution domain.
- Express a tie-broken optimizer relationally and prove totality and uniqueness
  instead of accepting an opaque selector witness.

## 9. Generalizations, Conjectures, and Extensions

The checked proposition is slightly stronger than the stated tie convention:
the rounded seat-share conclusion holds for every legal tie choice. No further
generalization is claimed.

## 10. Mathematical Typos or Other Fixes Suggested in the Source Paper

The appendix proof temporarily assumes turnout divisibility by `M + 1`, while
the proposition does not. The Lean proof supplies the missing floor-Droop
arithmetic under the proposition's stated turnout bound. This is a repaired
proof omission, not a status caveat.

## 11. Paper Issues or Caveats

None. The completed result preserves the advertised endpoint and strengthens
the tie handling.

## 12. Detailed Formalization Evidence

`paper_lemma_c1_pav_selector_eq_unique_integer_interval` proves the complete
PAV selector, interval, and uniqueness claim. The proposition route is
`paper_proposition1_all_ballot_routed_surplus_transfer_outcomes_and_selected_pav`;
it constructs the source initial state internally and does not accept a raw
run, party projection, conservation equality, local path, terminal party
count, or refinement certificate as a premise.

The v10 review surface has four current rows: a direct theorem and transparent
proposition specification for each named source item. Only the direct theorems
receive source coverage credit. The current source-record receipt is SHA256
`69a4560085372c924922a6cfb4a92c1466940e8036c6c17ede082875714313a5`.
It records 40 boundary inputs, two conclusion dependencies, 25 recursively
reviewed fields, no recursion failure, and no caller-supplied outcome premise.

## 13. Paper Assumption Provenance

No additional assumption supplies a stability, transfer, outcome, or rounded
seat-count conclusion.

<!-- BEGIN GENERATED ASSUMPTION PROVENANCE LEDGER -->
### Current Canonical Evidence
Generated from the configured source-condition surface and exact current statement digests in the canonical assumption-provenance sidecar. Model, agent, and automated checks are identified as such; no human review is inferred.

| Assumption declaration | Lean declaration | Source location / statement | Assumption validators | Comments |
| --- | --- | --- | --- | --- |
| None | `none` | None | None | No paper-facing assumption declarations are configured. |
<!-- END GENERATED ASSUMPTION PROVENANCE LEDGER -->

## 14. Displayed Formula Provenance

<!-- BEGIN GENERATED FORMULA PROVENANCE LEDGER -->
### Current Canonical Evidence
Rows are selected from semantic `formula` and `equation` source-kind metadata within the configured semantic source-coverage scope, never from declaration names. Coverage and statement checks remain separate evidence lanes. Active coverage mode: named theoretical statements.

| Paper formula / subclaim | Lean declaration | Provenance | Validators | Comments |
| --- | --- | --- | --- | --- |
| None | `none` | None | None | No source-map row is canonically classified as a formula or equation. |
<!-- END GENERATED FORMULA PROVENANCE LEDGER -->

## 15. Library Lift Pass

The reusable ballot-routed STV model and transfer-policy infrastructure remain
in the shared RCV library. Paper-specific party projection, solid-coalition
construction, and PAV comparison remain paper-local. The legacy raw-run API is
not a paper proof route.

## 16. DAG Audit

`docs/DependencyDAG.tex` and `docs/DependencyDAG.pdf` record the two named
results, their STV/PAV dependencies, the execution nonvacuity bridge, and the
deep-computational boundary. The current closeout records a rendered,
visually inspected artifact.

## 17. Validation Checks

Focused validation completed for the paper build, statement and assumption
prechecks, source coverage, evidence integrity, recursive source-record audit,
and consolidated paper closeout. No full-repository Lean build is claimed.
<!-- BEGIN GENERATED LLM-AS-JUDGE RESULTS -->
### LLM-as-Judge Results
- Source coverage (`audit/paper_coverage_llm.json`): 2 covered.
- Statement match (`audit/statement_match_llm.json`): 4 exact match.
- Lean-to-TeX translations (`audit/lean_to_tex_llm.json`): 4 row translations generated from Lean statements.
- Assumption provenance (`audit/assumption_match_llm.json`): no configured source-condition rows.
- Source-record classification (`audit/source_record_match_llm.json`): 42 source condition, 1 semantic model review, 1 source outcome domain.
- Source-record structural audit (`audit/source_record_audit.json`): 4 source-record review rows, 40 boundary inputs, 2 conclusion dependencies, 25 recursive fields, 2 semantic-model records, 1 source-record-only unresolved conclusion dependency, 0 recursion failures.
- Review-surface audit (`audit/review_surface_llm.json`): review surface passed over 4 review rows.
- Holistic source-first audit (`docs/AGENT_SOURCE_AUDIT.md`): status not inferred by this generator.
- DAG/source/source-json audit (`docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`): status not inferred by this generator.
<!-- END GENERATED LLM-AS-JUDGE RESULTS -->

## 18. Paper Definitions Checked

- The finite leftmost PAV maximizer and its harmonic score.
- Two-party solid-coalition ballots and party seat counts.
- Floor-Droop quota, ballot-routed election/elimination transitions, and legal
  terminal STV executions.

## 19. Named Theorem Statements Checked

### Lemma C.1

**Paper statement.** For `0 < y_R <= 1`, the leftmost PAV-maximizing
Republican seat count is the unique integer in the displayed half-open
interval.

**Lean interface statement.**
`paper_lemma_c1_pav_selector_eq_unique_integer_interval` states the selector,
interval, and uniqueness clauses together.

**Status.** Formalized.

### Proposition 1

**Paper statement.** Under the stated two-party turnout, candidate,
solid-coalition, and tie conditions, both STV and PAV Republican seat counts
are a floor or ceiling of proportional share.

**Lean interface statement.**
`paper_proposition1_all_ballot_routed_surplus_transfer_outcomes_and_selected_pav`
states both outcomes and quantifies over every legal terminal execution.

**Status.** Formalized.

## 20. Paper-Facing Statement Validator Ledger

The four rows are current automated-review evidence. Independent human review
is `0/4` and has not been fabricated or inferred.

<!-- BEGIN GENERATED STATEMENT VALIDATOR LEDGER -->
### Current Canonical Evidence
Independent human dashboard review: 0/4 rows. No human row-level approval is inferred. review surface passed; Agent check by Codex GGRS26 current semantic closeout auditor 2026-07-30; 2026-07-30

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| Lemma C.1: for y_R in (0,1], the paper's leftmost PAV maximizing Republican seat count equals the unique integer ell satisfying y_R(M+1)-1 <= ell < y_R(M+1). | `paper_lemma_c1_pav_selector_eq_unique_integer_interval` | exact match; Agent check by Codex GGRS26 current semantic closeout auditor 2026-07-30; 2026-07-30. Lean translation recorded; Agent check by Codex GGRS26 current elaborated-interface translator 2026-07-30; 2026-07-30 | The current declaration is source-equivalent after expanding the relational finite PAV maximizer, interval arithmetic, and uniqueness clauses. Every source input and manifest atom is listed and aligned below without relying on selector names. |
| - Lemma C.1 in its full source form: the finite leftmost PAV maximizer exists and is equal to the unique integer in the displayed half-open interval. The paper defines `n_R` by `min arg max`. The source-facing specification therefore quantifies over that relational definition, rather than exposing the implementation's `Classical.choose` witness. | `paper_lemma_c1_pav_selector_eq_unique_integer_intervalSpec` | exact match; Agent check by Codex GGRS26 current semantic closeout auditor 2026-07-30; 2026-07-30. Lean translation recorded; Agent check by Codex GGRS26 current elaborated-interface translator 2026-07-30; 2026-07-30 | The current declaration is source-equivalent after expanding the relational finite PAV maximizer, interval arithmetic, and uniqueness clauses. Every source input and manifest atom is listed and aligned below without relying on selector names. |
| Proposition 1: in a two-party M-seat district with V >= M(M+1), at least M candidates per party, solid coalitions, and D-favoring ties, both the STV and PAV Republican seat counts are in {floor(y_R M), ceil(y_R M)}. | `paper_proposition1_all_ballot_routed_surplus_transfer_outcomes_and_selected_pav` | exact match; Agent check by Codex GGRS26 current semantic closeout auditor 2026-07-30; 2026-07-30. Lean translation recorded; Agent check by Codex GGRS26 current elaborated-interface translator 2026-07-30; 2026-07-30 | The current declaration is source-equivalent after expanding the finite roster, transfer, canonical-initial-state, terminal-execution, relational-PAV, and rounded-seat semantics. All source inputs and every manifest atom are listed and aligned below; no condition is certified merely because a helper has a familiar name. |
| Proposition 1 (Seat shares under STV). Suppose – for a given district with M seats and V ≥ M (M + 1) voters – that a fraction yp of voters belong to each party p ∈ {R, D}, and that there are at least M candidates per party. Assume that each party’s voters rank all same-party candidates above all other-party candidates, and ties are broken in party D’s favor. Let nR (yR , ST V ) be the number of winners belonging t... | `paper_proposition1_all_ballot_routed_surplus_transfer_outcomes_and_selected_pavSpec` | exact match; Agent check by Codex GGRS26 current semantic closeout auditor 2026-07-30; 2026-07-30. Lean translation recorded; Agent check by Codex GGRS26 current elaborated-interface translator 2026-07-30; 2026-07-30 | The current declaration is source-equivalent after expanding the finite roster, transfer, canonical-initial-state, terminal-execution, relational-PAV, and rounded-seat semantics. All source inputs and every manifest atom are listed and aligned below; no condition is certified merely because a helper has a familiar name. |
<!-- END GENERATED STATEMENT VALIDATOR LEDGER -->

## 21. Source-Coverage Audit Ledger

- Source inventory: two distinct named results in the pinned source, plus one
  appendix presentation alias for Proposition 1.
- Coverage result: two covered named results; no conditional, missing, or
  support-only named-theory item.
- Scope exclusions: empirical, geographic, simulation, figure, implementation,
  and runtime claims are outside normal named-theory scope.
- Row-local checks: every linked review row has a current statement-match
  judgment.

<!-- BEGIN GENERATED SOURCE COVERAGE LEDGER -->
### Current Canonical Evidence
- Coverage scope: named theoretical statements.
- Source inventory: 2 source statements from `cited publication`.
- Coverage result: 2 covered.
- Coverage review: coverage ledger recorded; Agent check by Codex GGRS26 current semantic closeout auditor 2026-07-30; 2026-07-30.
- Row-local statement checks: 2/2 linked row references have a completed canonical statement check; repeated links are counted per source row.

| Source statement | Linked Lean review rows | Coverage judgment | Row-local statement checks | Comments |
| --- | --- | --- | --- | --- |
| Lemma C.1: for y_R in (0,1], the paper's leftmost PAV maximizing Republican seat count equals the unique integer ell satisfying y_R(M+1)-1 <= ell < y_R(M+1). | `paper_lemma_c1_pav_selector_eq_unique_integer_interval` | covered | `paper_lemma_c1_pav_selector_eq_unique_integer_interval`: exact match | The reviewed theorem endpoint proves the complete source-level statement with its displayed conditions and all conclusion components. The relational PAV selector/interval result is not reduced to an internal chosen witness. |
| Proposition 1: in a two-party M-seat district with V >= M(M+1), at least M candidates per party, solid coalitions, and D-favoring ties, both the STV and PAV Republican seat counts are in {floor(y_R M), ceil(y_R M)}. | `paper_proposition1_all_ballot_routed_surplus_transfer_outcomes_and_selected_pav` | covered | `paper_proposition1_all_ballot_routed_surplus_transfer_outcomes_and_selected_pav`: exact match | The reviewed theorem endpoint proves the complete source-level statement with its displayed conditions and all conclusion components. The endpoint starts executions from the constructed finite-electorate unit-weight state, quantifies lawful terminal outcomes, and ranges over relational PAV maximizers. |
<!-- END GENERATED SOURCE COVERAGE LEDGER -->
