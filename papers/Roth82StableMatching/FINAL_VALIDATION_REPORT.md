# Final Validation Report: Roth 1982

Updated: 2026-08-04

## 1. Human Verdict

**Formalized.** The normal paper-facing scope contains 21 theoretical items:
eleven paper-facing mathematical definitions and Theorems 1--7, Corollary
5.1, and Lemmas 1--2. Each item has a direct audited proposition and a separate
Lean proof in `PaperInterface.lean`. Five previously hidden domain problems
have been repaired. Theorem 3 now ranges over legal complete strict true and
reported profiles; Theorem 7 uses positive, distinct padding scores inside that
same source domain; the quota definition requires finite partner sets before
using finite cardinality; the efficiency definition ranges only over legal
strict reports; and Corollary 5.1 starts from and constructs legal reports. This
is an agent/code-backed verdict and does not claim independent human release
certification.

A second statement-surface pass repaired five additional fidelity defects.
The preference-profile and matching-procedure definitions now carry strict
profile legality and complete outcomes directly; Theorem 4 states the source's
existential conclusion without exposing its serial witness; and Theorem 5 and
Corollary 5.1 now include the side-optimal stable property of the procedures
whose incentive conclusions they state.

## 2. Closeout Status

- One-sentence recap: all 21 normal-scope source items are stated directly as
  audited propositions in `PaperInterface.lean` and proved without a hidden
  domain restriction or weakened conclusion.
- Completion status: formalized.
- Normal scope: 21 source items, comprising eleven definitions and ten named
  results.
- Human-facing theorem file: `PaperInterface.lean`.
- Review surface: 42 rows, one exact `Spec : Prop` and one proof for each
  normal source item.
- Lean footprint: 11,274 paper-local lines across six Lean files;
  `PaperInterface.lean` has 1,666 lines and 121 declarations, of which the
  configured normal review surface selects 42 rows.
- Automated evidence summary: 21/21 source items have direct paper-facing
  coverage and 42/42 normal statement rows have current statement judgments.
  The recursive audit adds two separately selected assumption rows, for 44
  configured structural rows. Its final source-record and closeout counts are
  reported in Section 17 from the frozen generated receipt.
- Independent human dashboard review: 0/42. This is release governance, not a
  mathematical or source-fidelity gap.

## 3. Source and Scope

The audited source is Alvin E. Roth, *The Economics of Matching: Stability and
Incentives*, *Mathematics of Operations Research* 7(4), 1982. The canonical
local source artifact is `Roth82StableMatching.txt`, SHA-256
`55d2c35a8077a74dc9953dcb6f838fcd6e91edc9e77079a2419f185835a79fd4`.
The source record is linked to https://doi.org/10.1287/moor.7.4.617.

Normal scope follows the repository's named-theory policy. It includes the
paper-facing definitions of the preference profile, matching procedure,
marriage model, complete outcome, stability, individual quotas, stable
procedure, dominant truthfulness, efficiency, side-optimality, and simple
misrepresentation, together with every numbered theorem, corollary, and lemma.
Algorithms, the Section 6 numerical example, proof-local notation, proof
narration, and unnumbered extension prose are deep-only unless needed to prove
one of those endpoints.

## 4. Researcher Summary of Checked Results

Theorems 1 and 2 establish existence of a stable complete matching and the
men-optimal and women-optimal stable outcomes for finite equal sides with
complete strict preferences. The source deferred-acceptance construction is
connected to the reusable matching library through an exact batched
waiting-list implementation, with the refinement proved rather than assumed.

Theorem 3 proves that no procedure can be both stable at every legal report
profile and dominant-strategy truthful for every agent on both sides. Theorem
4 constructs an efficient truthful serial procedure on the legal strict
domain. Theorem 5 proves truthfulness for the proposing side of its
side-optimal stable procedure. Corollary 5.1 starts from any legal report by an
agent on the other side and constructs another legal report preserving the
agent's true first choice whose outcome is weakly better under the agent's true
preference. Lemmas 1 and 2 formalize the
simple-misrepresentation reduction and its no-man-harmed comparison.

Theorem 6 proves that no complete feasible outcome is strictly better for
every man than the men-optimal stable outcome. Theorem 7 proves the
arbitrary-rank impossibility for every rank beyond first choice by extending
the three-by-three manipulation witness with positive, strictly ordered dummy
agents whose forced self-matches isolate the original core.

## 5. Remaining Boundaries and Gaps

No mathematical obligation remains in the configured normal named-theory
scope. The broad unnumbered assertion that all arguments carry over virtually
unchanged to arbitrary individual quotas is not used as source credit for a
general many-to-many incentive theorem. The paper's quota-outcome definition
is formalized with explicit finiteness of every partner set and exact finite
cardinality equal to the corresponding quota. The one-to-one
deferred-acceptance machinery used by the named results is checked through the
matching library. The exact many-to-one waiting-list runner is auxiliary quota
support. A future deep-paper review could formulate and prove a precise
responsive-preference theorem for the broad both-sided-quota model.

The proposal algorithms, termination narration, possible-partner notation,
serial-procedure narration, successful-misrepresentation shorthand, and the
Section 6 example remain support or deep-audit material under the normal-scope
policy. They are not missing named results.

## 6. Additional Assumptions Beyond Paper

There is no status-bearing additional economic assumption. The formalization
uses the following explicit source-model conventions:

1. Real-valued scores represent only ordinal rankings. Injectivity represents
   strict preference; numerical magnitudes have no economic meaning.
2. Positive scores, with zero reserved as the outside option in the reusable
   assignment library, encode the source marriage model in which every
   opposite-side agent is feasible and no complete marriage outcome leaves an
   agent unmatched. The source states complete strict orderings and complete
   outcomes rather than the literal inequality `0 < score`.
3. Equal cardinality is explicit in the marriage model. The general unmatched
   case is handled as the source suggests by padding with dummy agents, but all
   padding preferences used for theorem credit remain complete and strict.
4. The simple-report premise says exactly that the partner obtained under the
   original misreport is ranked first by the associated simple report.
5. The reusable `Assignment` carrier permits partial one-to-one assignments and
   is polymorphic over arbitrary carrier types. Source marriage endpoints are
   instantiated on finite equal sides and prove completeness; the generic
   carrier itself is not evidence for a source outcome.
6. Results that select an agent or a first choice use nonempty participant
   sides. This is the explicit Lean form of the source's named-agent and
   first-choice setup; it also prevents Theorem 6's strict "all men" comparison
   from becoming vacuous in the empty market.

`Fintype`, `DecidableEq`, and real-valued order encodings are finite
representation infrastructure, not matching conclusions supplied by a caller.

## 7. Proof-Strategy Deviations

Complex endpoints are stated once as exact audited propositions and proved as
separate theorems. Internal lemmas may decompose a proof, but source credit is
attached only to the complete proposition.

The reusable assignment library permits unmatched agents and uses zero as an
outside option. Roth's marriage model instead has complete outcomes and every
cross-side partner feasible. The paper-facing route therefore makes the legal
complete strict domain explicit and proves the required bridges rather than
letting sign conventions silently narrow a theorem.

Theorem 2 proves that operational stability and complete source stability agree
on the finite equal positive strict domain. Theorem 5 and Corollary 5.1 use the
same directly checked side-optimality lemmas as Theorem 2, and their own Specs
include the corresponding source-optimal stable property rather than relying
on a selector name. The serial procedure in Theorem 4 and the
batched proposal procedures used by Theorems 1, 2, 5, and 6 have separately
checked source-runner semantics and refinement theorems. No conclusion follows
from a selector or theorem name.

The broad quota paragraph is not represented by an arbitrary both-sided-quota
incentive theorem. A direct many-to-one batched waiting-list runner is used as
support for deferred acceptance, while the exact quota-outcome definition is
kept as its own source item.

## 8. Proof Tricks Worth Reusing

- Audit impossibility theorems against every true and reported profile used by
  the witness; a strictness condition on the true profile alone is not enough
  for a stable-procedure quantifier.
- When embedding a finite manipulation witness into a larger market, assign
  distinct positive fallback scores and force dummy self-matches through
  preference order. Do not use negative dummy scores when the source domain
  makes every pair feasible.
- State source definitions as closed equivalences and source theorems as closed
  propositions, then prove them separately. This exposes the full target even
  when the implementation uses many helper lemmas.
- Connect source algorithms to shared library implementations by a proved
  refinement theorem after establishing the source runner's own semantics.
- When a finite-cardinality API totalizes infinite sets, make finiteness an
  explicit conjunct before using its numeric result as a source quota.
- For incentive statements, audit both the original deviation and every
  existential replacement against the legal action space; checking only the
  truthful profile is insufficient.

## 9. Generalizations, Conjectures, and Extensions

The direct batched waiting-list runner and its refinement to applicant
deferred acceptance can support future many-to-one matching papers. A genuine
many-to-many version of Roth's broad quota sentence would require a precise
outcome model, responsive preferences over partner sets, acceptability and
outside-option conventions, and a separately proved stability and incentive
theorem. It is not obtained merely by cloning seats or renaming agents.

## 10. Mathematical Typos or Other Fixes Suggested in the Source Paper

None of the named theorem statements required a textual correction. The
source's terse proof of Theorem 7 says that examples can "obviously" be
constructed for every later rank; Lean supplies the missing positive-domain
padding construction. The broad quota-extension sentence is discussed in
Section 11 rather than treated as a corrected named theorem.

## 11. Paper Issues or Caveats

No status-bearing caveat remains. Section 2 also says that the arguments carry
over virtually unchanged to a more general model in which agents on both sides
may have individual quotas. The exact quota definition is coherent and is
formalized here. The broader unnumbered sentence is an unverified deep-only
generalization, not a named endpoint claimed by the normal closeout and not an
established defect in the paper.

Five earlier Lean formulations had formalization defects rather than source
theorem defects. Theorem 3 allowed the stability procedure to be tested on
reported score profiles outside the legal source domain. Theorem 7 padded the
arbitrary-rank construction with negative fallback scores even though the
complete marriage model treats every partner as feasible. The quota definition
used `Set.ncard` without requiring its partner sets finite, so an infinite set
could totalize to cardinality zero. The efficiency definition ranged over tied
and otherwise illegal reports. Corollary 5.1 did not require either the initial
misreport or the existential first-choice-preserving replacement to be legal.
All five defects are repaired in the current statements and proofs.

Five further source-facing surfaces were incomplete even though their internal
proof components existed. The preference-profile carrier omitted strictness;
the matching-procedure carrier returned a possibly partial assignment; Theorem
4 stated its particular serial construction rather than the paper's existential
claim; and Theorem 5 and Corollary 5.1 stated incentive conclusions without the
side-optimal stable property that identifies the procedures in the source.
Those Specs are now complete standalone propositions. The audit inventory was
also narrowed where it had combined the marriage-model domain with the separate
complete-outcome definition; that was an audit-metadata overclaim, not a paper
caveat.

## 12. Detailed Formalization Evidence

- The configured normal review surface in `PaperInterface.lean` selects exactly
  21 closed source propositions and their 21 distinct proof rows, covering
  eleven definitions and ten named results. The file contains additional
  declarations used to state and prove those propositions.
- `MainTheorems.lean` contains the repaired three-by-three Theorem 3 witness,
  the positive in-domain arbitrary-rank Theorem 7 construction, and the proof
  that raising the true first choice in a legal report preserves strictness and
  positivity.
- `GeneralMatching.lean` connects the source batched waiting-list procedure to
  the reusable deferred-acceptance library through a proved refinement.
- `SourceProcedures.lean` contains source-procedure support without receiving
  independent normal-scope coverage credit.
- `Assumptions.lean` exposes the equal-cardinality and simple-report conditions
  for separate source-provenance review.
- The v11 source map binds every source claim atom to the complete elaborated
  Spec closure; no declaration name is used as semantic evidence.
- A paper-local scan finds no `sorry`, `admit`, or declared axiom.

## 13. Paper Assumption Provenance

The paper-facing conditions are the equal finite sides and complete strict
preference profiles of the source marriage model, plus the exact
first-ranked-partner condition used by the source's simple-misrepresentation
reduction. Every true profile and every reported profile used by a stability
or incentive theorem is required to be legal. No stable outcome,
side-optimality conclusion, manipulation witness, or runner invariant is
accepted as a theorem premise.

<!-- BEGIN GENERATED ASSUMPTION PROVENANCE LEDGER -->
### Current Canonical Evidence
Generated from the configured source-condition surface and exact current statement digests in the canonical assumption-provenance sidecar. Model, agent, and automated checks are identified as such; no human review is inferred.

| Assumption declaration | Lean declaration | Source location / statement | Assumption validators | Comments |
| --- | --- | --- | --- | --- |
| Assumption equal cardinality | `assumption_equal_cardinality` | Source location: Roth82StableMatching.txt:176-197. - The source marriage-problem representation uses balanced one-to-one markets. This is the equal-size condition needed for complete strict-marriage endpoints. | source condition; Agent check by Codex Roth82 semantic premise provenance auditor 2026-08-04; 2026-08-04 | The expanded Lean proposition is equality of the finite cardinalities of the two sides. Roth's marriage-problem representation explicitly has equal numbers of men and women and excludes unmatched agents; the cardinality equality is therefore source-domain data, not a proof conclusion or an added regularity condition. Premise-level checks: 1 source condition |
| Assumption simple report ranks partner first | `assumption_simple_report_ranks_partner_first` | Source location: Roth82StableMatching.txt:522-529. - Roth's Lemma 1 simple-misrepresentation route assumes the simplified report strictly ranks the obtained partner first. | source condition; Agent check by Codex Roth82 semantic premise provenance auditor 2026-08-04; 2026-08-04 | The expanded Lean proposition says that the partner obtained under the original misreport is strictly ranked above every distinct alternative by the associated simple report. This is exactly the construction Roth specifies before Lemma 1, not a supplied proof of Lemma 1's same-partner conclusion. Premise-level checks: 1 source condition |
<!-- END GENERATED ASSUMPTION PROVENANCE LEDGER -->

## 14. Displayed Formula Provenance

The source has no separately selected displayed-equation item in the normal
inventory. Preference comparisons and blocking-pair clauses are audited inside
their complete definition or theorem proposition.

<!-- BEGIN GENERATED FORMULA PROVENANCE LEDGER -->
### Current Canonical Evidence
Rows are selected from semantic `formula` and `equation` source-kind metadata within the configured semantic source-coverage scope, never from declaration names. Coverage and statement checks remain separate evidence lanes. Active coverage mode: named theoretical statements.

| Paper formula / subclaim | Lean declaration | Provenance | Validators | Comments |
| --- | --- | --- | --- | --- |
| None | `none` | None | None | No source-map row is canonically classified as a formula or equation. |
<!-- END GENERATED FORMULA PROVENANCE LEDGER -->

## 15. Library Lift Pass

The paper reuses the shared assignment, stability, proposer-optimality, and
deferred-acceptance infrastructure. The exact paper-facing model bridges and
finite counterexamples remain paper-local so their source semantics are
inspectable. The source waiting-list runner is connected to the shared runner
only by a proved refinement; shared declaration names supply no paper credit.

## 16. DAG Audit

The dependency-DAG source is `docs/DependencyDAG.tex`, with rendered artifact
`docs/DependencyDAG.pdf`. It shows the 21 source items, the checked
deferred-acceptance support route, and the broad quota prose as deep-only. It
does not promote support algorithms or the unchecked deep-only general quota extension to
normal source results.

## 17. Validation Checks
<!-- BEGIN GENERATED LLM-AS-JUDGE RESULTS -->
### LLM-as-Judge Results
- Source coverage (`audit/paper_coverage_llm.json`): 21 covered.
- Statement match (`audit/statement_match_llm.json`): 42 exact match; source conditions: 2 source condition.
- Lean-to-TeX translations (`audit/lean_to_tex_llm.json`): 42 row translations generated from Lean statements; recorded translation metadata, whose independent freshness is not established by this report generator.
- Assumption provenance (`audit/assumption_match_llm.json`): 2 source condition.
- Source-record classification (`audit/source_record_match_llm.json`): 98 derived, 104 source condition, 2 non-propositional witness data, 23 semantic model review; recorded sidecar metadata, whose independent freshness is not established by this report generator.
- Source-record structural audit (`audit/source_record_audit.json`): 44 source-record review rows, 0 boundary inputs, 0 conclusion dependencies, 6 recursive fields, 23 semantic-model records, 0 source-record-only unresolved conclusion dependencies, 0 recursion failures; recorded structural metadata, whose independent freshness is not established by this report generator.
- Review-surface audit (`audit/review_surface_llm.json`): review surface passed over 44 review rows; recorded review-surface metadata, whose independent freshness is not established by this report generator.
- Holistic source-first audit (`docs/AGENT_SOURCE_AUDIT.md`): status not inferred by this generator.
- DAG/source/source-json audit (`docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`): status not inferred by this generator.
<!-- END GENERATED LLM-AS-JUDGE RESULTS -->


The frozen closeout surface passed the following checks on 2026-08-04:

- statement translation and semantic matching: 42/42 current exact rows;
- source inventory, coverage, and source-to-Lean routing: 21/21 direct items;
- assumption provenance: two visible source conditions and no hidden-premise
  finding;
- recursive source record: digest
  `2232929756e92ac1fb5390607148aca89893966f1b99830181114ce5464ee6e2`,
  with 227 current judgment groups covering all 204 theorem-realization
  components, six recursive fields, and zero unresolved source items,
  auxiliaries, conclusion dependencies, or recursion failures;
- conclusion provenance: `[]`;
- generic source-record scanner regression suite: 404 tests passed;
- focused `lake build Roth82StableMatching`: 3,316 jobs passed; and
- consolidated `--paper-closeout`: zero errors and one governance-only warning
  for incomplete independent human review.

Independent human dashboard review remains 0/42. Automated mathematical and
semantic closeout therefore passes, but this report does not claim human
release certification.

## 18. Paper Definitions Checked

| Normal-scope source item | Lean specification and proof | Status |
| --- | --- | --- |
| Preference profile | `preferenceProfile_eq_source_definitionSpec`, `preferenceProfile_eq_source_definition` | Formalized |
| Matching procedure | `matchingProcedure_eq_source_definitionSpec`, `matchingProcedure_eq_source_definition` | Formalized |
| Complete strict marriage model | `sourceMarriageModel_iff_source_definitionSpec`, `sourceMarriageModel_iff_source_definition` | Formalized |
| Complete marriage outcome | `completeMarriageOutcome_iff_source_definitionSpec`, `completeMarriageOutcome_iff_source_definition` | Formalized |
| Stable marriage | `sourceStableMarriage_iff_source_definitionSpec`, `sourceStableMarriage_iff_source_definition` | Formalized |
| Side-optimal stable outcome | `sideOptimalStableOutcome_iff_source_definitionSpec`, `sideOptimalStableOutcome_iff_source_definition` | Formalized |
| Outcome filling individual quotas | `fillsIndividualQuotas_iff_source_definitionSpec`, `fillsIndividualQuotas_iff_source_definition` | Formalized with explicit finite partner sets |
| Stable matching procedure | `sourceStableMatchingProcedure_iff_source_definitionSpec`, `sourceStableMatchingProcedure_iff_source_definition` | Formalized |
| Dominant truthfulness for all agents | `truthfulForAllAgents_iff_source_definitionSpec`, `truthfulForAllAgents_iff_source_definition` | Formalized on legal reports |
| Efficient matching procedure | `efficientMatchingProcedure_iff_source_definitionSpec`, `efficientMatchingProcedure_iff_source_definition` | Formalized on legal reports |
| Simple report ranking the obtained partner first | `manReportStrictlyRanksPartnerFirst_iff_source_definitionSpec`, `manReportStrictlyRanksPartnerFirst_iff_source_definition` | Formalized |

The general `Assignment` carrier, score-table aliases, operational stability,
and deferred-acceptance state machinery remain visible support vocabulary. They
do not create extra normal-scope source items.

## 19. Named Theorem Statements Checked

| Named source result | Lean specification and proof | Status |
| --- | --- | --- |
| Theorem 1: a stable marriage exists | `theorem1_stable_outcome_existsSpec`, `theorem1_stable_outcome_exists` | Formalized |
| Theorem 2: both side-optimal stable outcomes exist | `theorem2_side_optimal_stable_outcomesSpec`, `theorem2_side_optimal_stable_outcomes` | Formalized |
| Theorem 3: no stable procedure is truthful for all agents | `theorem3_no_stable_truthful_procedureSpec`, `theorem3_no_stable_truthful_procedure` | Formalized on legal true and reported profiles |
| Theorem 4: an efficient truthful procedure exists | `theorem4_efficient_truthful_procedure_existsSpec`, `theorem4_efficient_truthful_procedure_exists` | Formalized |
| Theorem 5: the optimal stable procedure is truthful for the proposing side | `theorem5_optimal_side_truthfulSpec`, `theorem5_optimal_side_truthful` | Formalized in both proposal directions |
| Corollary 5.1: a first choice need not be misrepresented | `corollary5_1_first_choice_need_not_be_misrepresentedSpec`, `corollary5_1_first_choice_need_not_be_misrepresented` | Formalized with legal initial and replacement reports |
| Lemma 1: the simple replacement report returns the same partner | `lemma1_simple_report_same_partnerSpec`, `lemma1_simple_report_same_partner` | Formalized |
| Lemma 2: a profitable simple report harms no man | `lemma2_simple_report_harms_no_manSpec`, `lemma2_simple_report_harms_no_man` | Formalized |
| Theorem 6: no outcome is strictly better for every man | `theorem6_no_outcome_strictly_better_for_all_menSpec`, `theorem6_no_outcome_strictly_better_for_all_men` | Formalized |
| Theorem 7: manipulation can occur at every rank after first | `theorem7_later_choice_manipulation_unavoidableSpec`, `theorem7_later_choice_manipulation_unavoidable` | Formalized with positive strict dummy padding |

## 20. Paper-Facing Statement Validator Ledger

The current review surface has one transparent specification and one proof row
for each of the 21 normal source items. The generated ledger below is owned by
the audit scripts; no human approval is inferred from automated evidence.

<!-- BEGIN GENERATED STATEMENT VALIDATOR LEDGER -->
### Current Canonical Evidence
Independent human dashboard review: 0/42 rows. No human row-level approval is inferred. review surface passed; Agent check by Independent Codex Roth82 semantic paper-facing surface auditor 2026-08-04; 2026-08-04

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| Section 2 Definition: the preference profile is the vector of strict preferences reported by every agent on both sides. | `preferenceProfile_eq_source_definitionSpec` | exact match; Agent check by Codex Roth82 fresh source-first expanded-semantics auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 fresh expanded-semantics translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | The complete expanded equality identifies the source preference profile with two side-indexed score tables and retains the strict, tie-free legality condition for every agent on both sides. |
| Section 2 Definition: the preference profile is the vector of strict preferences reported by every agent on both sides. | `preferenceProfile_eq_source_definition` | exact match; Agent check by Codex Roth82 fresh source-first expanded-semantics auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 fresh expanded-semantics translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | The complete expanded equality identifies the source preference profile with two side-indexed score tables and retains the strict, tie-free legality condition for every agent on both sides. |
| Section 4 Definition: a matching procedure elicits the agents reported preference profile and aggregates it to determine a matching outcome. | `matchingProcedure_eq_source_definitionSpec` | exact match; Agent check by Codex Roth82 fresh source-first expanded-semantics auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 fresh expanded-semantics translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | The complete expanded equality preserves both source restrictions: the input is a legal strict two-sided preference profile and the output is a complete one-to-one matching outcome. |
| Section 4 Definition: a matching procedure elicits the agents reported preference profile and aggregates it to determine a matching outcome. | `matchingProcedure_eq_source_definition` | exact match; Agent check by Codex Roth82 fresh source-first expanded-semantics auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 fresh expanded-semantics translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | The complete expanded equality preserves both source restrictions: the input is a legal strict two-sided preference profile and the output is a complete one-to-one matching outcome. |
| Section 2 model-domain definition: the marriage problem has equal finite sides and every agent has a complete transitive strict preference ordering, with no indifference between distinct potential partners. | `sourceMarriageModel_iff_source_definitionSpec` | exact match; Agent check by Codex Roth82 fresh source-first expanded-semantics auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 fresh expanded-semantics translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | The expanded equivalence covers exactly the balanced finite participant domain and complete strict preferences on both sides. Outcome completeness is a separate source item and is not claimed by this model-domain row. |
| Section 2 model-domain definition: the marriage problem has equal finite sides and every agent has a complete transitive strict preference ordering, with no indifference between distinct potential partners. | `sourceMarriageModel_iff_source_definition` | exact match; Agent check by Codex Roth82 fresh source-first expanded-semantics auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 fresh expanded-semantics translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | The expanded equivalence covers exactly the balanced finite participant domain and complete strict preferences on both sides. Outcome completeness is a separate source item and is not claimed by this model-domain row. |
| Section 2 Definition: a marriage outcome is a complete one-to-one matching between the two equal sides. | `completeMarriageOutcome_iff_source_definitionSpec` | exact match; Agent check by Codex Roth82 source-first semantic auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 context-free semantic translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | Source-first inspection of the pinned passage and every canonical signature atom found the same participant domain, explicit source conditions, quantifier scope, assignment semantics, strict and weak preference directions, witnesses, and full conclusion. Equal cardinality, positivity as the no-unmatched encoding, and simple-report-first are recorded where they occur rather than hidden in an endpoint. |
| Section 2 Definition: a marriage outcome is a complete one-to-one matching between the two equal sides. | `completeMarriageOutcome_iff_source_definition` | exact match; Agent check by Codex Roth82 source-first semantic auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 context-free semantic translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | Source-first inspection of the pinned passage and every canonical signature atom found the same participant domain, explicit source conditions, quantifier scope, assignment semantics, strict and weak preference directions, witnesses, and full conclusion. Equal cardinality, positivity as the no-unmatched encoding, and simple-report-first are recorded where they occur rather than hidden in an endpoint. |
| Section 2 Definition: a complete marriage outcome is stable exactly when no unmatched man-woman pair both strictly prefer one another to their assigned partners. | `sourceStableMarriage_iff_source_definitionSpec` | exact match; Agent check by Codex Roth82 source-first semantic auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 context-free semantic translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | Source-first inspection of the pinned passage and every canonical signature atom found the same participant domain, explicit source conditions, quantifier scope, assignment semantics, strict and weak preference directions, witnesses, and full conclusion. Equal cardinality, positivity as the no-unmatched encoding, and simple-report-first are recorded where they occur rather than hidden in an endpoint. |
| Section 2 Definition: a complete marriage outcome is stable exactly when no unmatched man-woman pair both strictly prefer one another to their assigned partners. | `sourceStableMarriage_iff_source_definition` | exact match; Agent check by Codex Roth82 source-first semantic auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 context-free semantic translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | Source-first inspection of the pinned passage and every canonical signature atom found the same participant domain, explicit source conditions, quantifier scope, assignment semantics, strict and weak preference directions, witnesses, and full conclusion. Equal cardinality, positivity as the no-unmatched encoding, and simple-report-first are recorded where they occur rather than hidden in an endpoint. |
| Section 4 Definition: an outcome is side-optimal stable when it is stable and every member of the selected side weakly prefers it to every other stable outcome. | `sideOptimalStableOutcome_iff_source_definitionSpec` | exact match; Agent check by Codex Roth82 source-first semantic auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 context-free semantic translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | Source-first inspection of the pinned passage and every canonical signature atom found the same participant domain, explicit source conditions, quantifier scope, assignment semantics, strict and weak preference directions, witnesses, and full conclusion. Equal cardinality, positivity as the no-unmatched encoding, and simple-report-first are recorded where they occur rather than hidden in an endpoint. |
| Section 4 Definition: an outcome is side-optimal stable when it is stable and every member of the selected side weakly prefers it to every other stable outcome. | `sideOptimalStableOutcome_iff_source_definition` | exact match; Agent check by Codex Roth82 source-first semantic auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 context-free semantic translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | Source-first inspection of the pinned passage and every canonical signature atom found the same participant domain, explicit source conditions, quantifier scope, assignment semantics, strict and weak preference directions, witnesses, and full conclusion. Equal cardinality, positivity as the no-unmatched encoding, and simple-report-first are recorded where they occur rather than hidden in an endpoint. |
| Section 2 Definition: in the broad general matching model, each agent has an individual quota and is matched with exactly that many partners, with mutually consistent pair membership. | `fillsIndividualQuotas_iff_source_definitionSpec` | exact match; Agent check by Independent Codex Roth82 semantic statement auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 context-free semantic translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | The byte-pinned source defines a quota outcome by assigning every agent exactly the stated number of partners. The repaired Lean surface makes finiteness explicit before using finite cardinality on both sides, so Set.ncard's total value on an infinite set cannot satisfy a quota accidentally; mutual membership consistency remains part of the assignment carrier. |
| Section 2 Definition: in the broad general matching model, each agent has an individual quota and is matched with exactly that many partners, with mutually consistent pair membership. | `fillsIndividualQuotas_iff_source_definition` | exact match; Agent check by Independent Codex Roth82 semantic statement auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 context-free semantic translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | The byte-pinned source defines a quota outcome by assigning every agent exactly the stated number of partners. The repaired Lean surface makes finiteness explicit before using finite cardinality on both sides, so Set.ncard's total value on an infinite set cannot satisfy a quota accidentally; mutual membership consistency remains part of the assignment carrier. |
| Section 4 Definition: a stable matching procedure returns an outcome stable with respect to every reported preference profile. | `sourceStableMatchingProcedure_iff_source_definitionSpec` | exact match; Agent check by Codex Roth82 source-first semantic auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 context-free semantic translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | Source-first inspection of the pinned passage and every canonical signature atom found the same participant domain, explicit source conditions, quantifier scope, assignment semantics, strict and weak preference directions, witnesses, and full conclusion. Equal cardinality, positivity as the no-unmatched encoding, and simple-report-first are recorded where they occur rather than hidden in an endpoint. |
| Section 4 Definition: a stable matching procedure returns an outcome stable with respect to every reported preference profile. | `sourceStableMatchingProcedure_iff_source_definition` | exact match; Agent check by Codex Roth82 source-first semantic auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 context-free semantic translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | Source-first inspection of the pinned passage and every canonical signature atom found the same participant domain, explicit source conditions, quantifier scope, assignment semantics, strict and weak preference directions, witnesses, and full conclusion. Equal cardinality, positivity as the no-unmatched encoding, and simple-report-first are recorded where they occur rather than hidden in an endpoint. |
| Section 4 Definition: truthful revelation is dominant when no unilateral misreport can give an agent a better outcome under that agent's true preferences, regardless of the other reports. | `truthfulForAllAgents_iff_source_definitionSpec` | exact match; Agent check by Codex Roth82 source-first semantic auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 context-free semantic translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | Source-first inspection of the pinned passage and every canonical signature atom found the same participant domain, explicit source conditions, quantifier scope, assignment semantics, strict and weak preference directions, witnesses, and full conclusion. Equal cardinality, positivity as the no-unmatched encoding, and simple-report-first are recorded where they occur rather than hidden in an endpoint. |
| Section 4 Definition: truthful revelation is dominant when no unilateral misreport can give an agent a better outcome under that agent's true preferences, regardless of the other reports. | `truthfulForAllAgents_iff_source_definition` | exact match; Agent check by Codex Roth82 source-first semantic auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 context-free semantic translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | Source-first inspection of the pinned passage and every canonical signature atom found the same participant domain, explicit source conditions, quantifier scope, assignment semantics, strict and weak preference directions, witnesses, and full conclusion. Equal cardinality, positivity as the no-unmatched encoding, and simple-report-first are recorded where they occur rather than hidden in an endpoint. |
| Section 4 Definition: an efficient matching procedure always returns a Pareto-optimal complete outcome. | `efficientMatchingProcedure_iff_source_definitionSpec` | exact match; Agent check by Independent Codex Roth82 semantic statement auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 context-free semantic translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | The repaired quantifier ranges over exactly the source-legal marriage profiles: every score row is strict and every partner is preferred to the unmatched value. Within that domain the expanded proposition requires completeness and excludes a complete assignment that weakly improves all participants and strictly improves at least one; it does not substitute stability for Pareto efficiency. |
| Section 4 Definition: an efficient matching procedure always returns a Pareto-optimal complete outcome. | `efficientMatchingProcedure_iff_source_definition` | exact match; Agent check by Independent Codex Roth82 semantic statement auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 context-free semantic translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | The repaired quantifier ranges over exactly the source-legal marriage profiles: every score row is strict and every partner is preferred to the unmatched value. Within that domain the expanded proposition requires completeness and excludes a complete assignment that weakly improves all participants and strictly improves at least one; it does not substitute stability for Pareto efficiency. |
| Section 5 Definition: the simple report associated with a unilateral misrepresentation ranks the partner obtained from that misrepresentation strictly above every other possible partner. | `manReportStrictlyRanksPartnerFirst_iff_source_definitionSpec` | exact match; Agent check by Codex Roth82 source-first semantic auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 context-free semantic translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | Source-first inspection of the pinned passage and every canonical signature atom found the same participant domain, explicit source conditions, quantifier scope, assignment semantics, strict and weak preference directions, witnesses, and full conclusion. Equal cardinality, positivity as the no-unmatched encoding, and simple-report-first are recorded where they occur rather than hidden in an endpoint. |
| Section 5 Definition: the simple report associated with a unilateral misrepresentation ranks the partner obtained from that misrepresentation strictly above every other possible partner. | `manReportStrictlyRanksPartnerFirst_iff_source_definition` | exact match; Agent check by Codex Roth82 source-first semantic auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 context-free semantic translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | Source-first inspection of the pinned passage and every canonical signature atom found the same participant domain, explicit source conditions, quantifier scope, assignment semantics, strict and weak preference directions, witnesses, and full conclusion. Equal cardinality, positivity as the no-unmatched encoding, and simple-report-first are recorded where they occur rather than hidden in an endpoint. |
| Theorem 1: the set of stable outcomes is always nonempty. | `theorem1_stable_outcome_existsSpec` | exact match; Agent check by Codex Roth82 source-first semantic auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 context-free semantic translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | Source-first inspection of the pinned passage and every canonical signature atom found the same participant domain, explicit source conditions, quantifier scope, assignment semantics, strict and weak preference directions, witnesses, and full conclusion. Equal cardinality, positivity as the no-unmatched encoding, and simple-report-first are recorded where they occur rather than hidden in an endpoint. |
| Theorem 1: the set of stable outcomes is always nonempty. | `theorem1_stable_outcome_exists` | exact match; Agent check by Codex Roth82 source-first semantic auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 context-free semantic translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | Source-first inspection of the pinned passage and every canonical signature atom found the same participant domain, explicit source conditions, quantifier scope, assignment semantics, strict and weak preference directions, witnesses, and full conclusion. Equal cardinality, positivity as the no-unmatched encoding, and simple-report-first are recorded where they occur rather than hidden in an endpoint. |
| Theorem 2: one stable outcome is weakly preferred by every man to every other stable outcome, and a symmetric stable outcome exists for every woman. | `theorem2_side_optimal_stable_outcomesSpec` | exact match; Agent check by Codex Roth82 source-first semantic auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 context-free semantic translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | Source-first inspection of the pinned passage and every canonical signature atom found the same participant domain, explicit source conditions, quantifier scope, assignment semantics, strict and weak preference directions, witnesses, and full conclusion. Equal cardinality, positivity as the no-unmatched encoding, and simple-report-first are recorded where they occur rather than hidden in an endpoint. |
| Theorem 2: one stable outcome is weakly preferred by every man to every other stable outcome, and a symmetric stable outcome exists for every woman. | `theorem2_side_optimal_stable_outcomes` | exact match; Agent check by Codex Roth82 source-first semantic auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 context-free semantic translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | Source-first inspection of the pinned passage and every canonical signature atom found the same participant domain, explicit source conditions, quantifier scope, assignment semantics, strict and weak preference directions, witnesses, and full conclusion. Equal cardinality, positivity as the no-unmatched encoding, and simple-report-first are recorded where they occur rather than hidden in an endpoint. |
| Theorem 3: no stable matching procedure makes truthful revelation a dominant strategy for all agents. | `theorem3_no_stable_truthful_procedureSpec` | exact match; Agent check by Codex Roth82 source-first semantic auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 context-free semantic translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | Source-first inspection of the pinned passage and every canonical signature atom found the same participant domain, explicit source conditions, quantifier scope, assignment semantics, strict and weak preference directions, witnesses, and full conclusion. Equal cardinality, positivity as the no-unmatched encoding, and simple-report-first are recorded where they occur rather than hidden in an endpoint. |
| Theorem 3: no stable matching procedure makes truthful revelation a dominant strategy for all agents. | `theorem3_no_stable_truthful_procedure` | exact match; Agent check by Codex Roth82 source-first semantic auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 context-free semantic translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | Source-first inspection of the pinned passage and every canonical signature atom found the same participant domain, explicit source conditions, quantifier scope, assignment semantics, strict and weak preference directions, witnesses, and full conclusion. Equal cardinality, positivity as the no-unmatched encoding, and simple-report-first are recorded where they occur rather than hidden in an endpoint. |
| Theorem 4: efficient matching procedures exist for which truthful revelation is a dominant strategy for every agent. | `theorem4_efficient_truthful_procedure_existsSpec` | exact match; Agent check by Codex Roth82 source-first semantic auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 Theorem 4 semantic translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | Source-first comparison of the pinned Theorem 4 passage with the complete canonical result graph found the same existential output shape: for every finite balanced market, one procedure witness is efficient on every legal strict profile and dominant-strategy truthful for every agent on both sides. Serial dictatorship occurs only as the proof witness, and the closed source-facing proposition receives no extra premise. |
| Theorem 4: efficient matching procedures exist for which truthful revelation is a dominant strategy for every agent. | `theorem4_efficient_truthful_procedure_exists` | exact match; Agent check by Codex Roth82 source-first semantic auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 Theorem 4 semantic translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | Source-first comparison of the pinned Theorem 4 passage with the complete canonical result graph found the same existential output shape: for every finite balanced market, one procedure witness is efficient on every legal strict profile and dominant-strategy truthful for every agent on both sides. Serial dictatorship occurs only as the proof witness, and the closed source-facing proposition receives no extra premise. |
| Theorem 5: the procedure selecting the optimal stable outcome for either side makes truthful revelation dominant for all agents on that side. | `theorem5_optimal_side_truthfulSpec` | exact match; Agent check by Codex Roth82 fresh source-first expanded-semantics auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 fresh expanded-semantics translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | The expanded endpoint contains both proposal directions, each procedure's side-optimal stable-outcome conjunct, and the corresponding universal dominant-truthfulness inequality over every legal unilateral report. |
| Theorem 5: the procedure selecting the optimal stable outcome for either side makes truthful revelation dominant for all agents on that side. | `theorem5_optimal_side_truthful` | exact match; Agent check by Codex Roth82 fresh source-first expanded-semantics auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 fresh expanded-semantics translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | The expanded endpoint contains both proposal directions, each procedure's side-optimal stable-outcome conjunct, and the corresponding universal dominant-truthfulness inequality over every legal unilateral report. |
| Corollary 5.1: under a side-optimal stable procedure, agents on the other side have no incentive to misrepresent their first choice. | `corollary5_1_first_choice_need_not_be_misrepresentedSpec` | exact match; Agent check by Codex Roth82 fresh source-first expanded-semantics auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 fresh expanded-semantics translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | The expanded endpoint contains both side-optimality conjuncts and, in each opposite-side direction, quantifies every legal report, constructs a legal strict positive replacement preserving the true first choice, and proves the replacement outcome weakly better under the deviator's true ordering. |
| Corollary 5.1: under a side-optimal stable procedure, agents on the other side have no incentive to misrepresent their first choice. | `corollary5_1_first_choice_need_not_be_misrepresented` | exact match; Agent check by Codex Roth82 fresh source-first expanded-semantics auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 fresh expanded-semantics translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | The expanded endpoint contains both side-optimality conjuncts and, in each opposite-side direction, quantifies every legal report, constructs a legal strict positive replacement preserving the true first choice, and proves the replacement outcome weakly better under the deviator's true ordering. |
| Lemma 1: replacing a report by the associated simple report that ranks the obtained partner first leaves the manipulator matched to the same partner. | `lemma1_simple_report_same_partnerSpec` | exact match; Agent check by Codex Roth82 source-first semantic auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 context-free semantic translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | Source-first inspection of the pinned passage and every canonical signature atom found the same participant domain, explicit source conditions, quantifier scope, assignment semantics, strict and weak preference directions, witnesses, and full conclusion. Equal cardinality, positivity as the no-unmatched encoding, and simple-report-first are recorded where they occur rather than hidden in an endpoint. |
| Lemma 1: replacing a report by the associated simple report that ranks the obtained partner first leaves the manipulator matched to the same partner. | `lemma1_simple_report_same_partner` | exact match; Agent check by Codex Roth82 source-first semantic auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 context-free semantic translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | Source-first inspection of the pinned passage and every canonical signature atom found the same participant domain, explicit source conditions, quantifier scope, assignment semantics, strict and weak preference directions, witnesses, and full conclusion. Equal cardinality, positivity as the no-unmatched encoding, and simple-report-first are recorded where they occur rather than hidden in an endpoint. |
| Lemma 2: if a simple misrepresentation leaves its author weakly better off, every man is weakly better off under the resulting outcome. | `lemma2_simple_report_harms_no_manSpec` | exact match; Agent check by Codex Roth82 source-first semantic auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 context-free semantic translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | Source-first inspection of the pinned passage and every canonical signature atom found the same participant domain, explicit source conditions, quantifier scope, assignment semantics, strict and weak preference directions, witnesses, and full conclusion. Equal cardinality, positivity as the no-unmatched encoding, and simple-report-first are recorded where they occur rather than hidden in an endpoint. |
| Lemma 2: if a simple misrepresentation leaves its author weakly better off, every man is weakly better off under the resulting outcome. | `lemma2_simple_report_harms_no_man` | exact match; Agent check by Codex Roth82 source-first semantic auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 context-free semantic translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | Source-first inspection of the pinned passage and every canonical signature atom found the same participant domain, explicit source conditions, quantifier scope, assignment semantics, strict and weak preference directions, witnesses, and full conclusion. Equal cardinality, positivity as the no-unmatched encoding, and simple-report-first are recorded where they occur rather than hidden in an endpoint. |
| Theorem 6: no feasible outcome is strictly preferred by every man to the men-optimal deferred-acceptance outcome. | `theorem6_no_outcome_strictly_better_for_all_menSpec` | exact match; Agent check by Codex Roth82 source-first semantic auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 context-free semantic translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | Source-first inspection of the pinned passage and every canonical signature atom found the same participant domain, explicit source conditions, quantifier scope, assignment semantics, strict and weak preference directions, witnesses, and full conclusion. Equal cardinality, positivity as the no-unmatched encoding, and simple-report-first are recorded where they occur rather than hidden in an endpoint. |
| Theorem 6: no feasible outcome is strictly preferred by every man to the men-optimal deferred-acceptance outcome. | `theorem6_no_outcome_strictly_better_for_all_men` | exact match; Agent check by Codex Roth82 source-first semantic auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 context-free semantic translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | Source-first inspection of the pinned passage and every canonical signature atom found the same participant domain, explicit source conditions, quantifier scope, assignment semantics, strict and weak preference directions, witnesses, and full conclusion. Equal cardinality, positivity as the no-unmatched encoding, and simple-report-first are recorded where they occur rather than hidden in an endpoint. |
| Theorem 7: for every rank k other than first choice, no stable matching procedure can avoid giving some agent an incentive to misrepresent that kth choice on every instance. | `theorem7_later_choice_manipulation_unavoidableSpec` | exact match; Agent check by Codex Roth82 source-first semantic auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 context-free semantic translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | Source-first inspection of the pinned passage and every canonical signature atom found the same participant domain, explicit source conditions, quantifier scope, assignment semantics, strict and weak preference directions, witnesses, and full conclusion. Equal cardinality, positivity as the no-unmatched encoding, and simple-report-first are recorded where they occur rather than hidden in an endpoint. |
| Theorem 7: for every rank k other than first choice, no stable matching procedure can avoid giving some agent an incentive to misrepresent that kth choice on every instance. | `theorem7_later_choice_manipulation_unavoidable` | exact match; Agent check by Codex Roth82 source-first semantic auditor 2026-08-04; 2026-08-04. Lean translation recorded; Agent check by Codex Roth82 context-free semantic translator 2026-08-04; 2026-08-04; recorded translation metadata, whose independent freshness is not established by this report generator | Source-first inspection of the pinned passage and every canonical signature atom found the same participant domain, explicit source conditions, quantifier scope, assignment semantics, strict and weak preference directions, witnesses, and full conclusion. Equal cardinality, positivity as the no-unmatched encoding, and simple-report-first are recorded where they occur rather than hidden in an endpoint. |
| - The source marriage-problem representation uses balanced one-to-one markets. This is the equal-size condition needed for complete strict-marriage endpoints. | `assumption_equal_cardinality` | source condition; Agent check by Codex Roth82 semantic premise provenance auditor 2026-08-04; 2026-08-04 | The expanded Lean proposition is equality of the finite cardinalities of the two sides. Roth's marriage-problem representation explicitly has equal numbers of men and women and excludes unmatched agents; the cardinality equality is therefore source-domain data, not a proof conclusion or an added regularity condition. |
| - Roth's Lemma 1 simple-misrepresentation route assumes the simplified report strictly ranks the obtained partner first. | `assumption_simple_report_ranks_partner_first` | source condition; Agent check by Codex Roth82 semantic premise provenance auditor 2026-08-04; 2026-08-04 | The expanded Lean proposition says that the partner obtained under the original misreport is strictly ranked above every distinct alternative by the associated simple report. This is exactly the construction Roth specifies before Lemma 1, not a supplied proof of Lemma 1's same-partner conclusion. |
<!-- END GENERATED STATEMENT VALIDATOR LEDGER -->

## 21. Source-Coverage Audit Ledger

The normal inventory contains eleven paper-facing mathematical definitions and
ten named theoretical results. Every item routes to a direct specification and
proof in `PaperInterface.lean`. Algorithms, numerical examples, proof-local
notation, and unnumbered extension prose receive no normal-coverage credit.

<!-- BEGIN GENERATED SOURCE COVERAGE LEDGER -->
### Current Canonical Evidence
- Coverage scope: named theoretical statements.
- Source inventory: 21 source statements from `Roth82StableMatching.txt`.
- Coverage result: 21 covered.
- Coverage review: coverage ledger recorded; Agent check by Independent Codex Roth82 source-to-surface semantic auditor 2026-08-04; 2026-08-04.
- Row-local statement checks: 21/21 linked row references have a completed canonical statement check; repeated links are counted per source row.

| Source statement | Linked Lean review rows | Coverage judgment | Row-local statement checks | Comments |
| --- | --- | --- | --- | --- |
| Theorem 1: the set of stable outcomes is always nonempty. | `theorem1_stable_outcome_exists` | covered | `theorem1_stable_outcome_exists`: exact match | The closed proposition quantifies over arbitrary finite balanced strict complete-marriage markets and concludes existence of an Assignment that is complete and has no two-sided blocking pair. Positivity is the score encoding of the source domain in which every potential partner is preferred to being unmatched. |
| Theorem 2: one stable outcome is weakly preferred by every man to every other stable outcome, and a symmetric stable outcome exists for every woman. | `theorem2_side_optimal_stable_outcomes` | covered | `theorem2_side_optimal_stable_outcomes`: exact match | The closed proposition supplies both a men-side and a women-side stable outcome. Each is weakly best for every member of its side among all stable outcomes, and balanced-domain completeness is included, so neither symmetric half nor the stable-completeness endpoint is missing. |
| Theorem 3: no stable matching procedure makes truthful revelation a dominant strategy for all agents. | `theorem3_no_stable_truthful_procedure` | covered | `theorem3_no_stable_truthful_procedure`: exact match | The closed proposition negates existence of a mechanism that is stable at every legal profile and dominant-strategy truthful for every agent on both sides. Its fixed finite counterexample domain is a valid witness to the source's universal nonexistence claim and does not assume a candidate mechanism's failure. |
| Theorem 4: efficient matching procedures exist for which truthful revelation is a dominant strategy for every agent. | `theorem4_efficient_truthful_procedure_exists` | covered | `theorem4_efficient_truthful_procedure_exists`: exact match | The selected closed proposition quantifies a matching-procedure witness for each finite balanced market and requires that witness to satisfy the audited efficiency and all-agent dominant-truthfulness definitions. Its proof constructs serial dictatorship as the witness; the source-facing conclusion does not hardcode the implementation. |
| Theorem 5: the procedure selecting the optimal stable outcome for either side makes truthful revelation dominant for all agents on that side. | `theorem5_optimal_side_truthful` | covered | `theorem5_optimal_side_truthful`: exact match | The endpoint now includes the source side-optimal stable-outcome fact for each proposal direction before proving the same side's universal no-gain result. Neither optimality conjunct is supplied by a theorem-facing premise. |
| Corollary 5.1: under a side-optimal stable procedure, agents on the other side have no incentive to misrepresent their first choice. | `corollary5_1_first_choice_need_not_be_misrepresented` | covered | `corollary5_1_first_choice_need_not_be_misrepresented`: exact match | Both proposal directions explicitly include their source side-optimal stable outcome and the complete first-choice-preserving replacement result. The new equal-cardinality premise is the source balanced-marriage condition. |
| Lemma 1: replacing a report by the associated simple report that ranks the obtained partner first leaves the manipulator matched to the same partner. | `lemma1_simple_report_same_partner` | covered | `lemma1_simple_report_same_partner`: exact match | Given the partner produced by an arbitrary report, the closed proposition assumes the associated simple report strictly ranks that partner above every alternative and proves the two reports return the same partner. The simple-report-first condition is exactly the source's construction condition. |
| Lemma 2: if a simple misrepresentation leaves its author weakly better off, every man is weakly better off under the resulting outcome. | `lemma2_simple_report_harms_no_man` | covered | `lemma2_simple_report_harms_no_man`: exact match | On a balanced strict complete-marriage domain, the closed proposition assumes a simple report, its returned top partner, and weak improvement for the reporter, then concludes weak improvement for every man. It retains the source antecedent and the all-men endpoint. |
| Theorem 6: no feasible outcome is strictly preferred by every man to the men-optimal deferred-acceptance outcome. | `theorem6_no_outcome_strictly_better_for_all_men` | covered | `theorem6_no_outcome_strictly_better_for_all_men`: exact match | The closed proposition rules out every complete feasible Assignment that all men strictly prefer to the men-proposing deferred-acceptance outcome. The comparison ranges over stable and unstable feasible outcomes, preserving the theorem's stronger weak-Pareto conclusion. |
| Theorem 7: for every rank k other than first choice, no stable matching procedure can avoid giving some agent an incentive to misrepresent that kth choice on every instance. | `theorem7_later_choice_manipulation_unavoidable` | covered | `theorem7_later_choice_manipulation_unavoidable`: exact match | For every rank strictly beyond first, the closed proposition produces a finite balanced strict complete-marriage market in which every stable procedure exposes some profitable report changing that rank. The quantifier order preserves an instance against arbitrary stable procedures rather than selecting a favorable procedure. |
| Section 2 Definition: the preference profile is the vector of strict preferences reported by every agent on both sides. | `preferenceProfile_eq_source_definition` | covered | `preferenceProfile_eq_source_definition`: exact match | The expanded equality includes both sides' score tables and both rowwise injectivity conditions, so it covers the source vector of strict preferences rather than an unrestricted pair of functions. |
| Section 2 Definition: a marriage outcome is a complete one-to-one matching between the two equal sides. | `completeMarriageOutcome_iff_source_definition` | covered | `completeMarriageOutcome_iff_source_definition`: exact match | The elaborated proposition requires every man to have some woman and every woman to have some man in the mutually consistent Assignment representation. Thus the reviewed endpoint is a complete one-to-one marriage outcome, not merely a partial matching. |
| Section 2 Definition: a complete marriage outcome is stable exactly when no unmatched man-woman pair both strictly prefer one another to their assigned partners. | `sourceStableMarriage_iff_source_definition` | covered | `sourceStableMarriage_iff_source_definition`: exact match | The elaborated proposition conjoins completeness with the negation of an existential man-woman pair for which both strict score comparisons favor one another over their assigned partners. It neither weakens the two-sided blocking condition nor substitutes operational individual rationality for the source definition. |
| Section 2 Definition: in the broad general matching model, each agent has an individual quota and is matched with exactly that many partners, with mutually consistent pair membership. | `fillsIndividualQuotas_iff_source_definition` | covered | `fillsIndividualQuotas_iff_source_definition`: exact match | The byte-pinned source defines a quota outcome by assigning every agent exactly the stated number of partners. The repaired Lean surface makes finiteness explicit before using finite cardinality on both sides, so Set.ncard's total value on an infinite set cannot satisfy a quota accidentally; mutual membership consistency remains part of the assignment carrier. |
| Section 4 Definition: a stable matching procedure returns an outcome stable with respect to every reported preference profile. | `sourceStableMatchingProcedure_iff_source_definition` | covered | `sourceStableMatchingProcedure_iff_source_definition`: exact match | The elaborated proposition quantifies over every legal two-sided reported profile and requires the mechanism's complete outcome to have no blocking pair at that same profile. The conclusion is procedure-wide stability, not stability of one supplied run. |
| Section 4 Definition: truthful revelation is dominant when no unilateral misreport can give an agent a better outcome under that agent's true preferences, regardless of the other reports. | `truthfulForAllAgents_iff_source_definition` | covered | `truthfulForAllAgents_iff_source_definition`: exact match | The elaborated proposition covers unilateral reports by agents on either side and compares each deviating outcome under that agent's true score table with the truthful outcome, holding the other reports fixed. Both action domains and both dominant-strategy inequalities are present. |
| Section 4 Definition: an efficient matching procedure always returns a Pareto-optimal complete outcome. | `efficientMatchingProcedure_iff_source_definition` | covered | `efficientMatchingProcedure_iff_source_definition`: exact match | The repaired quantifier ranges over exactly the source-legal marriage profiles: every score row is strict and every partner is preferred to the unmatched value. Within that domain the expanded proposition requires completeness and excludes a complete assignment that weakly improves all participants and strictly improves at least one; it does not substitute stability for Pareto efficiency. |
| Section 5 Definition: the simple report associated with a unilateral misrepresentation ranks the partner obtained from that misrepresentation strictly above every other possible partner. | `manReportStrictlyRanksPartnerFirst_iff_source_definition` | covered | `manReportStrictlyRanksPartnerFirst_iff_source_definition`: exact match | The elaborated proposition states that the partner obtained under the original misreport is strictly above every distinct alternative in the associated simple report. It is the full top-partner condition used by the source, not merely preservation of relative ranks below the top. |
| Section 4 Definition: a matching procedure elicits the agents reported preference profile and aggregates it to determine a matching outcome. | `matchingProcedure_eq_source_definition` | covered | `matchingProcedure_eq_source_definition`: exact match | The expanded function type has the exact legal-profile input and complete-outcome codomain. It therefore does not broaden the source procedure to arbitrary score tables or partial assignments. |
| Section 4 Definition: an outcome is side-optimal stable when it is stable and every member of the selected side weakly prefers it to every other stable outcome. | `sideOptimalStableOutcome_iff_source_definition` | covered | `sideOptimalStableOutcome_iff_source_definition`: exact match | The elaborated proposition includes stability and comparison with every other stable outcome, pointwise for every member of the selected side, and states the symmetric men and women forms. The relation is weak side-wide optimality, not aggregate welfare. |
| Section 2 model-domain definition: the marriage problem has equal finite sides and every agent has a complete transitive strict preference ordering, with no indifference between distinct potential partners. | `sourceMarriageModel_iff_source_definition` | covered | `sourceMarriageModel_iff_source_definition`: exact match | The proposition exactly covers finite equal cardinality and both sides' complete strict tie-free preferences. It intentionally gives no credit for complete outcomes, which have their own separately reviewed definition. |
<!-- END GENERATED SOURCE COVERAGE LEDGER -->
