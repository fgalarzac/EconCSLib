# Final Validation Report: Gale-Shapley 1962

Updated: 2026-08-04

## 1. Human Verdict

**Formalized.** The normal paper-facing scope contains five source-presented
theoretical items: the two displayed college definitions, the Section 3 prose
definition of an unstable marriage, Theorem 1, and Theorem 2. Each has a direct
Lean specification and proof route. Theorem 2 now runs through a literal
Section 4 state machine that retains exactly the top quota-many applicants from
the old waiting list and the new application batch. No source-paper caveat is
needed. This is an agent/code-backed verdict and does not claim independent
human release certification.

## 2. Closeout Status

- Completion status: Formalized.
- Normal scope: five source items, comprising three definitions and two named
  theorems.
- Human-facing theorem file: `PaperInterface.lean`.
- Current automated evidence: five of five source items covered, ten of ten
  paper-facing rows judged exact, and 69 source-record judgments bound to 64
  theorem-realization components.
- Focused paper build and consolidated paper closeout: passed with zero errors.
  The remaining `0/10` human-review count is release governance, not a proof or
  source-fidelity gap.

## 3. Source and Scope

The audited source is D. Gale and L. S. Shapley, *College Admissions and the
Stability of Marriage*, *American Mathematical Monthly* 69(1), 1962, printed
pages 9--15. The local scan is `source.pdf`, SHA-256
`953a8123e8120a86b17ae3de92cb51abb5aed420fe11b97fe2a666a8e637d09b`.
Its checked transcript is `source.txt`, SHA-256
`9774fb809c349d8d56ebf758e912018958b7b2353d325ccfa65ffc6b37bfe799`.
The scan was rendered and inspected page by page, including the repaired
Section 4 procedure text and the concluding printed page 15. The public record
is https://www.jstor.org/stable/2312726.

Normal scope follows the repository's named-theory policy. It includes the
paper's displayed Definitions on printed page 10, the result-bearing Section 3
prose definition, and Theorems 1--2. The three numerical examples and
unnumbered procedure consequences remain available as support and deep-audit
material, but they neither earn normal-scope coverage credit nor block this
closeout.

## 4. Researcher Summary of Checked Results

The marriage definition says an assignment is unstable exactly when a man and
woman prefer one another to their actual mates. Theorem 1 is formalized for two
distinct finite sides of equal cardinality with complete strict preferences;
it returns a complete assignment with no such pair.

For college admissions, Lean separately exposes the literal displayed
replacement-pair instability definition and the literal applicant-optimality
definition over fixed-quota feasible assignments. The Theorem 2 route makes
the paper's intended completed stability convention explicit: quota
feasibility, individual rationality, and no mutually acceptable block through
either a vacancy or replacement of a current assignee.

The Section 4 algorithm is now modeled directly. Its state stores cumulative
applications, each round sends every active applicant to the best mutually
eligible college not yet tried, and each college's new waiting list is exactly
the top `q` of its previous waiting list union the new applications. Lean proves
termination, the reachable-state and rejection invariants, stability of the
terminal assignment, applicant optimality, and equality with the independently
proved refined-seat deferred-acceptance outcome.

## 5. Remaining Boundaries and Gaps

No mathematical obligation remains in the configured normal scope. Examples
and unnumbered prose claims are intentionally deep-only under the normal-scope
policy, even where support proofs already exist. Independent human dashboard
review is release-governance work, not missing mathematics.

The post-freeze v11 source-to-Spec correspondence, statement, coverage,
source-record, conclusion-provenance, evidence-integrity, focused-build, and
consolidated-closeout checks are complete. They report no unresolved
mathematical or automated-evidence defect.

## 6. Additional Assumptions Beyond Paper

There is no status-bearing additional economic assumption. The formalization
uses two explicit representation conventions:

1. `GS62-STRICT-LIST-NUMERIC-EXTENSION-01` represents strict ordered lists by
   real scores, with positive scores for listed alternatives, negative scores
   for omitted alternatives, and zero as the outside option. Lean also gives
   omitted alternatives an arbitrary strict numeric order. That extension is
   behaviorally irrelevant because omitted pairs cannot enter the source
   procedure.
2. `GS62-MUTUAL-APPLICATION-ELIGIBILITY-01` reads a permitted application as a
   pair listed by both the applicant and the college. This is a pairwise filter
   on applications, matching Section 4; it is not the stronger global premise
   that every college acceptable to an applicant must accept that applicant.

`Fintype`, `DecidableEq`, and natural-valued quotas are representation
infrastructure for the finite communities and quotas in the paper.

## 7. Proof-Strategy Deviations

The first college implementation refined each college into named seats and ran
the seats sequentially. That construction remains useful as an independent
deferred-acceptance characterization, but it is not itself the source's
simultaneous top-`q` stage semantics. The remediation therefore added a direct
source state machine and proves equality with the refined-seat outcome only
after proving the source runner's own invariants, stability, and optimality.

The completed stability convention used in Theorem 2 is kept separate from the
literal page-10 replacement-pair predicate. The proof does not silently treat
those predicates as definitionally identical.

## 8. Proof Tricks Worth Reusing

- Model cumulative applications and define the waiting list as a pure top-`q`
  choice from that history; this makes the source round equation exact.
- Use strict decrease of the finite set of untried eligible pairs as the
  termination measure.
- Carry a rejection invariant: once a pair is rejected, no stable comparison
  assignment can match that applicant to that college.
- Derive stability and applicant optimality directly from the terminal state,
  then use uniqueness of applicant-optimal values to identify the result with
  an independently implemented deferred-acceptance runner.
- Keep literal source definitions and completed operational conventions on
  separate paper-facing rows when the source proof relies on the completion.

## 9. Generalizations, Conjectures, and Extensions

The direct finite top-`q` runner, termination measure, and rejection invariant
are candidates for extraction into the shared many-to-one matching library.
That refactoring is not required for the GS62 result.

## 10. Mathematical Typos or Other Fixes Suggested in the Source Paper

None found. The stability completion discussed below is an interpretation made
explicit by the paper's procedure and proof, not a proposed change to its main
result.

## 11. Paper Issues or Caveats

No status-bearing caveat remains. The literal page-10 replacement-pair
definition mentions two currently assigned applicants and therefore, taken in
isolation, does not exclude unacceptable assignments, vacancy blocks, or
blocks by unmatched applicants. The procedure and Theorem 2 are formalized
with the completed standard stability reading that the argument requires,
while the literal displayed definition is also formalized separately and the
one-way implication from completed stability to literal stability is proved.
This is recorded as formalized interpretation note
`GS62-LITERAL-STABILITY-COMPLETION-01`, not as a paper caveat.

The prior Lean implementation had a formalization defect, not a source-paper
defect: during a cloned-seat stage an applicant could be displaced after the
implementation had stopped consuming that college's remaining seat proposals,
then reapply in a later stage. Consequently the old block transition was not
the advertised exact top-`q` source round. The new direct runner repairs this
and the paper-facing Theorem 2 endpoint no longer relies on the mislabeled
stage semantics.

## 12. Detailed Formalization Evidence

- `PaperInterface.lean` exposes the five normal source items through direct
  specifications and proofs, with procedure support visible but outside the
  counted surface.
- `ExactCollegeBatchedProcedure.lean` defines the direct Section 4 state,
  top-`q` transition, finite terminal runner, rejection invariant, terminal
  assignment, stability theorem, applicant-optimality theorem, and equality to
  the independent refined-seat deferred-acceptance outcome.
- `SourceStability.lean` keeps the literal page-10 definition separate from
  completed standard stability and proves the valid implication between them.
- `SourceCompletion.lean` supplies the complete strict marriage domain and the
  Theorem 1 route for distinct equal-cardinality sides.
- Independent proof review checked the source-round equation, termination
  measure, rejection invariant, terminal stability/optimality chain, and the
  absence of a global applicant-positive-implies-college-positive premise.
- A paper-local source scan finds no `sorry`, `admit`, or declared axiom.

## 13. Paper Assumption Provenance

The theorem premises are the finite strict preference domains and equal-side
cardinality stated by the source model. Pairwise mutual eligibility is built
into the Section 4 procedure rather than supplied as a global theorem
assumption. The numeric strict-score extension is a representation convention
whose extra ordering of omitted alternatives cannot affect an application or
terminal assignment.

<!-- BEGIN GENERATED ASSUMPTION PROVENANCE LEDGER -->
### Current Canonical Evidence
Generated from the configured source-condition surface and exact current statement digests in the canonical assumption-provenance sidecar. Model, agent, and automated checks are identified as such; no human review is inferred.

| Assumption declaration | Lean declaration | Source location / statement | Assumption validators | Comments |
| --- | --- | --- | --- | --- |
| None | `none` | None | None | No paper-facing assumption declarations are configured. |
<!-- END GENERATED ASSUMPTION PROVENANCE LEDGER -->

## 14. Displayed Formula Provenance

The two displayed page-10 definitions have direct proposition specifications.
Theorem 2's procedure atom preserves the exact top-`q` update, pairwise mutual
eligibility, preference-order advancement, and terminal applicant comparison.
The normal source inventory contains no separately selected displayed-equation
item.

<!-- BEGIN GENERATED FORMULA PROVENANCE LEDGER -->
### Current Canonical Evidence
Rows are selected from semantic `formula` and `equation` source-kind metadata within the configured semantic source-coverage scope, never from declaration names. Coverage and statement checks remain separate evidence lanes. Active coverage mode: named theoretical statements.

| Paper formula / subclaim | Lean declaration | Provenance | Validators | Comments |
| --- | --- | --- | --- | --- |
| None | `none` | None | None | No source-map row is canonically classified as a formula or equation. |
<!-- END GENERATED FORMULA PROVENANCE LEDGER -->

## 15. Library Lift Pass

The implementation reuses shared assignments, stability, one-to-one deferred
acceptance, many-to-one seat refinement, and applicant optimality. The exact
source state and its invariants remain paper-local so the audited procedure is
inspectable without treating a shared certificate as the source algorithm.
The independent refined-seat proof is used only after the direct source runner
has been proved stable and applicant-optimal.

## 16. DAG Audit

The dependency-DAG source is `docs/DependencyDAG.tex`, with rendered artifact
`docs/DependencyDAG.pdf`. The refreshed graph shows the five-item normal source
surface, routes Theorem 2 through the direct Section 4 runner, and labels the
legacy cloned-seat construction as auxiliary. The rendered PDF was inspected
after regeneration.

## 17. Validation Checks
<!-- BEGIN GENERATED LLM-AS-JUDGE RESULTS -->
### LLM-as-Judge Results
- Source coverage (`audit/paper_coverage_llm.json`): 5 covered.
- Statement match (`audit/statement_match_llm.json`): 10 exact match.
- Lean-to-TeX translations (`audit/lean_to_tex_llm.json`): 10 row translations generated from Lean statements; recorded translation metadata, whose independent freshness is not established by this report generator.
- Assumption provenance: no assumption-match sidecar tracked for this paper.
- Source-record classification (`audit/source_record_match_llm.json`): 31 derived, 29 source condition, 4 non-propositional witness data, 5 semantic model review; recorded sidecar metadata, whose independent freshness is not established by this report generator.
- Source-record structural audit (`audit/source_record_audit.json`): 10 source-record review rows, 0 boundary inputs, 0 conclusion dependencies, 6 recursive fields, 5 semantic-model records, 0 source-record-only unresolved conclusion dependencies, 0 recursion failures; recorded structural metadata, whose independent freshness is not established by this report generator.
- Review-surface audit (`audit/review_surface_llm.json`): review surface passed over 10 review rows; recorded review-surface metadata, whose independent freshness is not established by this report generator.
- Holistic source-first audit (`docs/AGENT_SOURCE_AUDIT.md`): status not inferred by this generator.
- DAG/source/source-json audit (`docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`): status not inferred by this generator.
<!-- END GENERATED LLM-AS-JUDGE RESULTS -->

- The materially changed `ExactCollegeBatchedProcedure.lean` elaborated under
  the pinned Lean toolchain, followed by successful focused elaboration of the
  importing `PaperInterface.lean`.
- The proof surface was independently reviewed for the source top-`q` update,
  termination and rejection invariants, terminal stability, applicant
  optimality, and the refined-seat equality bridge.
- The paper-local Lean files contain no `sorry`, `admit`, or declared axiom.
- The targeted command
  `env LEAN_NUM_THREADS=1 SYSTEMD_LOG_TARGET=null lake build GS62CollegeAdmissions`
  passes. Lean replays a known toolchain panic diagnostic from `Examples.lean`,
  but the build exits successfully and builds the paper target.
- The final consolidated closeout command is
  `env LEAN_NUM_THREADS=1 SYSTEMD_LOG_TARGET=null python3 scripts/audit_repository.py --paper GS62CollegeAdmissions --paper-closeout --include-active --info-limit 0 --closeout-trace`.
  It passed after the final surface freeze with zero errors and one expected
  governance warning for `0/10` independent human review. The closeout reused
  all 26 requested semantic closures and all eight requested Lean-graph
  receipts.
- The final recursive source-record audit contains 69 judgments over 64 bound
  realization components, with zero unresolved conclusion dependencies, zero
  recursion failures, and zero conclusion-provenance findings.

## 18. Paper Definitions Checked

| Normal-scope source item | Lean specification and proof | Status |
| --- | --- | --- |
| Displayed unstable college assignment definition | `unstableCollegeAssignment_iff_source_definitionSpec`, `unstableCollegeAssignment_iff_source_definition` | Formalized literally |
| Displayed applicant-optimal stable assignment definition | `literalApplicantOptimalCollegeAssignment_iff_source_definitionSpec`, `literalApplicantOptimalCollegeAssignment_iff_source_definition` | Formalized literally over feasible fixed-quota assignments |
| Section 3 prose definition of unstable marriage | `unstableMarriage_iff_source_definitionSpec`, `unstableMarriage_iff_source_definition` | Formalized literally on the complete marriage domain |

Completed marriage/college stability predicates, feasibility, strict domains,
and the pairwise application filter remain visible support vocabulary. They do
not create extra normal-scope source items.

## 19. Named Theorem Statements Checked

### Theorem 1

**Paper statement.** Every finite complete strict equal-side marriage market
has a stable set of marriages.

**Lean interface.** `theorem1_stable_marriage_existsSpec` states the full
distinct-carrier, equal-cardinality obligation;
`theorem1_stable_marriage_exists` proves it.

**Status.** Formalized.

### Theorem 2

**Paper statement.** Every applicant is at least as well off under the
assignment returned by the Section 4 deferred-acceptance procedure as under
any other stable assignment.

**Lean interface.** `theorem2_applicant_optimalitySpec` exposes the exact
one-round relation and reachability from the empty application history. It
asserts that a reachable terminal state exists and that every reachable
terminal state's proof-free assignment view is applicant-optimal under the
completed-standard stability comparison. `theorem2_applicant_optimality`
proves this full arbitrary-quota statement; the terminating recursive runner
is proof support rather than a hidden source-facing premise.

**Status.** Formalized. The literal displayed stability definition is also
formalized separately; the completion used here is the documented
`GS62-LITERAL-STABILITY-COMPLETION-01` interpretation note.

## 20. Paper-Facing Statement Validator Ledger

The v11 review surface has one transparent specification and one proof row for
each of the five normal source items. The generated ledger below is owned by
the audit scripts; no human approval is inferred from automated evidence.

<!-- BEGIN GENERATED STATEMENT VALIDATOR LEDGER -->
### Current Canonical Evidence
Independent human dashboard review: 0/10 rows. No human row-level approval is inferred. review surface passed; Agent check by Codex GS62 review-surface auditor 2026-08-04; 2026-08-04

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| Displayed Definition: an assignment is unstable when applicants alpha and beta are assigned to colleges A and B, respectively, beta prefers A to B, and A prefers beta to alpha. | `unstableCollegeAssignment_iff_source_definitionSpec` | exact match; Agent check by Codex GS62 semantic statement auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex GS62 context-free statement translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | A source-first comparison of the pinned presentation with the complete elaborated signature and transparent dependency closure found the same domains, quantifiers, premises, matching objects, preference directions, and complete endpoint. Literal replacement stability is kept separate from completed-standard stability; the college procedure uses mutual eligibility and the exact batched top-quota terminal state. |
| Displayed Definition: an assignment is unstable when applicants alpha and beta are assigned to colleges A and B, respectively, beta prefers A to B, and A prefers beta to alpha. | `unstableCollegeAssignment_iff_source_definition` | exact match; Agent check by Codex GS62 semantic statement auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex GS62 context-free statement translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | A source-first comparison of the pinned presentation with the complete elaborated signature and transparent dependency closure found the same domains, quantifiers, premises, matching objects, preference directions, and complete endpoint. Literal replacement stability is kept separate from completed-standard stability; the college procedure uses mutual eligibility and the exact batched top-quota terminal state. |
| Displayed Definition: within the fixed-quota feasible domain, a literally stable assignment is optimal when every applicant is at least as well off under it as under every other literally stable feasible assignment. | `literalApplicantOptimalCollegeAssignment_iff_source_definitionSpec` | exact match; Agent check by Codex GS62 semantic statement auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex GS62 context-free statement translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | A source-first comparison of the pinned presentation with the complete elaborated signature and transparent dependency closure found the same domains, quantifiers, premises, matching objects, preference directions, and complete endpoint. Literal replacement stability is kept separate from completed-standard stability; the college procedure uses mutual eligibility and the exact batched top-quota terminal state. |
| Displayed Definition: within the fixed-quota feasible domain, a literally stable assignment is optimal when every applicant is at least as well off under it as under every other literally stable feasible assignment. | `literalApplicantOptimalCollegeAssignment_iff_source_definition` | exact match; Agent check by Codex GS62 semantic statement auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex GS62 context-free statement translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | A source-first comparison of the pinned presentation with the complete elaborated signature and transparent dependency closure found the same domains, quantifiers, premises, matching objects, preference directions, and complete endpoint. Literal replacement stability is kept separate from completed-standard stability; the college procedure uses mutual eligibility and the exact batched top-quota terminal state. |
| Section 3 prose Definition: a set of marriages is unstable when some man and woman are not married to each other but both prefer each other to their actual mates. | `unstableMarriage_iff_source_definitionSpec` | exact match; Agent check by Codex GS62 semantic statement auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex GS62 context-free statement translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | A source-first comparison of the pinned presentation with the complete elaborated signature and transparent dependency closure found the same domains, quantifiers, premises, matching objects, preference directions, and complete endpoint. Literal replacement stability is kept separate from completed-standard stability; the college procedure uses mutual eligibility and the exact batched top-quota terminal state. |
| Section 3 prose Definition: a set of marriages is unstable when some man and woman are not married to each other but both prefer each other to their actual mates. | `unstableMarriage_iff_source_definition` | exact match; Agent check by Codex GS62 semantic statement auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex GS62 context-free statement translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | A source-first comparison of the pinned presentation with the complete elaborated signature and transparent dependency closure found the same domains, quantifiers, premises, matching objects, preference directions, and complete endpoint. Literal replacement stability is kept separate from completed-standard stability; the college procedure uses mutual eligibility and the exact batched top-quota terminal state. |
| Theorem 1: for two finite equally sized communities in which every participant strictly ranks every member of the opposite side, there exists a complete set of marriages with no mutually preferable unmatched pair. | `theorem1_stable_marriage_existsSpec` | exact match; Agent check by Codex GS62 semantic statement auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex GS62 context-free statement translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | A source-first comparison of the pinned presentation with the complete elaborated signature and transparent dependency closure found the same domains, quantifiers, premises, matching objects, preference directions, and complete endpoint. Literal replacement stability is kept separate from completed-standard stability; the college procedure uses mutual eligibility and the exact batched top-quota terminal state. |
| Theorem 1: for two finite equally sized communities in which every participant strictly ranks every member of the opposite side, there exists a complete set of marriages with no mutually preferable unmatched pair. | `theorem1_stable_marriage_exists` | exact match; Agent check by Codex GS62 semantic statement auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex GS62 context-free statement translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | A source-first comparison of the pinned presentation with the complete elaborated signature and transparent dependency closure found the same domains, quantifiers, premises, matching objects, preference directions, and complete endpoint. Literal replacement stability is kept separate from completed-standard stability; the college procedure uses mutual eligibility and the exact batched top-quota terminal state. |
| Theorem 2: the Section 4 arbitrary-quota applicant-proposing waiting-list procedure returns a completed-standard stable assignment under which every applicant is at least as well off as under every other completed-standard stable assignment. | `theorem2_applicant_optimalitySpec` | exact match; Agent check by Codex GS62 semantic statement auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex GS62 context-free statement translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | A source-first comparison of the pinned presentation with the complete elaborated signature and transparent dependency closure found the same domains, quantifiers, premises, matching objects, preference directions, and complete endpoint. Literal replacement stability is kept separate from completed-standard stability; the college procedure uses mutual eligibility and the exact batched top-quota terminal state. |
| Theorem 2: the Section 4 arbitrary-quota applicant-proposing waiting-list procedure returns a completed-standard stable assignment under which every applicant is at least as well off as under every other completed-standard stable assignment. | `theorem2_applicant_optimality` | exact match; Agent check by Codex GS62 semantic statement auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex GS62 context-free statement translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | A source-first comparison of the pinned presentation with the complete elaborated signature and transparent dependency closure found the same domains, quantifiers, premises, matching objects, preference directions, and complete endpoint. Literal replacement stability is kept separate from completed-standard stability; the college procedure uses mutual eligibility and the exact batched top-quota terminal state. |
<!-- END GENERATED STATEMENT VALIDATOR LEDGER -->

## 21. Source-Coverage Audit Ledger

The current normal source inventory has five selected theoretical items. Each
routes to a direct specification and proof in `PaperInterface.lean`. Examples,
the printed runtime sentence, unequal-side consequences, side-optimality prose,
and the inverted-procedure discussion are deep/support scope and receive no
normal-coverage credit.

<!-- BEGIN GENERATED SOURCE COVERAGE LEDGER -->
### Current Canonical Evidence
- Coverage scope: named theoretical statements.
- Source inventory: 5 source statements from `source.txt`.
- Coverage result: 5 covered.
- Coverage review: coverage ledger recorded; Agent check by Codex GS62 five-item semantic coverage auditor 2026-08-04; 2026-08-04.
- Row-local statement checks: 5/5 linked row references have a completed canonical statement check; repeated links are counted per source row.

| Source statement | Linked Lean review rows | Coverage judgment | Row-local statement checks | Comments |
| --- | --- | --- | --- | --- |
| Displayed Definition: an assignment is unstable when applicants alpha and beta are assigned to colleges A and B, respectively, beta prefers A to B, and A prefers beta to alpha. | `unstableCollegeAssignment_iff_source_definition` | covered | `unstableCollegeAssignment_iff_source_definition`: exact match | The reviewed theorem proves the exact unfolding of the displayed replacement-pair predicate. Its proposition retains both current assignments and both strict improvements and does not import vacancy, unmatched-applicant, or individual-rationality clauses from completed stability. |
| Displayed Definition: within the fixed-quota feasible domain, a literally stable assignment is optimal when every applicant is at least as well off under it as under every other literally stable feasible assignment. | `literalApplicantOptimalCollegeAssignment_iff_source_definition` | covered | `literalApplicantOptimalCollegeAssignment_iff_source_definition`: exact match | The reviewed theorem proves the displayed applicant-optimality definition over the surrounding fixed-quota feasible domain. It keeps literal page-10 stability for both the candidate and every comparison assignment and quantifies the applicant-by-applicant weak-preference conclusion. |
| Theorem 1: for two finite equally sized communities in which every participant strictly ranks every member of the opposite side, there exists a complete set of marriages with no mutually preferable unmatched pair. | `theorem1_stable_marriage_exists` | covered | `theorem1_stable_marriage_exists`: exact match | The reviewed theorem covers distinct finite marriage-side types, assumes equal cardinality and complete strict cross-side preferences, and produces a complete assignment with no mutually preferable unmatched pair. Thus both the source domain and the existence conclusion are in the proved proposition. |
| Theorem 2: the Section 4 arbitrary-quota applicant-proposing waiting-list procedure returns a completed-standard stable assignment under which every applicant is at least as well off as under every other completed-standard stable assignment. | `theorem2_applicant_optimality` | covered | `theorem2_applicant_optimality`: exact match | The reviewed theorem proves applicant optimality for the exact Section 4 batched runner: applications are mutually eligible and best-first, every round retains each college's top quota from its old waiting list plus new applications, and the terminal assignment is compared applicant-by-applicant with every completed-standard stable assignment. The completed stability reading is explicitly recorded rather than smuggled into the page-10 definition. |
| Section 3 prose Definition: a set of marriages is unstable when some man and woman are not married to each other but both prefer each other to their actual mates. | `unstableMarriage_iff_source_definition` | covered | `unstableMarriage_iff_source_definition`: exact match | The reviewed theorem proves the exact existential prose definition: there is a man and woman whose values for one another strictly exceed the values of their current mates. It neither substitutes completed operational stability nor weakens the two-sided improvement. |
<!-- END GENERATED SOURCE COVERAGE LEDGER -->
