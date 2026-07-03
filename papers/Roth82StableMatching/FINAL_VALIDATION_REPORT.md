# Final Validation Report: Roth 1982 Matching

Updated: 2026-07-03

## 1. Human Verdict
Formalized. Roth's named Theorems 1--7, Lemmas 1--2, and Corollary 5.1 are
checked on the paper's strict one-to-one marriage domain. No source-paper error
is reported. Human dashboard sign-off has not been recorded; the current
LLM-as-judge, source-coverage, source-record, holistic, and DAG audits are
summarized below.

## 2. Closeout Status
- Completion status: formalized.
- One-sentence recap: Roth's stable-matching, incentive, and reduction results are formalized through the shared deferred-acceptance library.
- Lean footprint: 8,931 paper-local Lean LOC; `PaperInterface.lean` is 490 lines; 29 human-review declarations are exposed.
- Audit summary: source coverage has 29 covered; statement LLM-as-judge has 29 matches; Lean-to-TeX has 27 row translations; assumption provenance has 2 paper_condition; source-record classification sidecar is not tracked; source-record audit reports 29 review rows, 0 boundary inputs, 0 recursion failures; review-surface audit passes over 29 review rows; holistic source-first audit PASS; DAG/source-json audit PASS in `docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`.

## 3. Source and Scope
- Paper: *The Economics of Matching: Stability and Incentives* (Roth 1982)
- Source version: Mathematics of Operations Research, Vol. 7, No. 4 (Nov., 1982)
- Lean folder: `papers/Roth82StableMatching/`
- Human-facing theorem file: `papers/Roth82StableMatching/PaperInterface.lean`
- Post-paper audit ledger: `papers/Roth82StableMatching/PostPaperAudit.lean`,
  imported by `papers/Roth82StableMatching.lean`
- DAG source/rendered output: tracked
  `papers/Roth82StableMatching/docs/DependencyDAG.tex` and
  `papers/Roth82StableMatching/docs/DependencyDAG.pdf`; other local LaTeX build
  artifacts are ignored by the paper-folder `.gitignore`

## 4. Researcher Summary of Checked Results
- Roth's named Theorems 1-7, Lemmas 1-2, and Corollary 5.1 are checked on the paper's strict one-to-one marriage domain.
- The proof builds on the shared matching library while keeping the paper-facing result inventory explicit.
- No source-paper error is recorded for the checked theorem surface.

## 5. Remaining Boundaries and Gaps
None.

## 6. Additional Assumptions Beyond Paper
None.

## 7. Proof-Strategy Deviations
None. The formalization follows Roth's deferred-acceptance, role-reversal,
strict-report, serial-dictatorship, and padding arguments. The implementation
breaks those arguments into reusable invariants and paper-facing wrappers, but
that is proof organization rather than a substantive departure from the source
proof strategy.

## 8. Proof Tricks Worth Reusing
- Use reusable deferred-acceptance invariants for paper proofs that reason about
  rejected pairs, proposal monotonicity, termination, and proposer optimality.
- Keep `PaperInterface.lean` at the source-paper granularity and move
  source-numbered aliases, compatibility wrappers, and proof-seam endpoints into
  `PostPaperAudit.lean`.
- Separate source-domain endpoints from broader compatibility APIs when a paper
  works on strict marriage domains but the reusable library primitives support
  arbitrary utility profiles.
- Use side-swapping and role-reversal lemmas to expose symmetric men/women
  theorem statements without duplicating the full DA proof.
- For padded manipulation families, expose a readable rank-misreport predicate,
  a family certificate, and a direct source-facing arbitrary-`k` theorem rather
  than asking reviewers to inspect the padding construction.

## 9. Mathematical Typos or Other Fixes Suggested in the Source Paper
None found.

## 10. Paper Issues or Caveats
None found.

## 11. Detailed Formalization Evidence
### Proof Organization Notes

- Theorem 2 uses a reusable DA rejected-pair-impossibility invariant for Roth's
  "possible woman" induction; the women side is obtained by side swap and
  role-reversed deferred acceptance.
- Theorems 3 and 7 follow Roth's finite counterexample route. Lean makes the
  stable-set enumeration, manipulation contradiction, and arbitrary-`k` padding
  explicit.
- Theorem 4 is closed by an indexed finite-marriage serial dictatorship over
  `Fin n`, while broader certificate wrappers remain available only as
  compatibility APIs.
- Theorem 5, Lemmas 1--2, and Corollary 5.1 are decomposed into source-domain
  strict-report, no-harm, trace-split, and top-choice persistence lemmas. These
  are formal proof-organization details, not deviations from Roth's strategy.
- Theorem 6 follows Roth's final active proposal step: Lean derives DA
  completeness, the final unmatched-woman trace fact, the final unique-proposal
  observation, and weak Pareto optimality.

### Post-Paper Audit Checklist

- Local cached-text named-result inventory:
  Theorem 1 (line 227), Theorem 2 (line 258), Theorem 3 (line 356),
  Theorem 4 (line 438), Theorem 5 (line 468), Corollary 5.1 (line 477),
  Lemma 1 (line 537), Lemma 2 (line 564), Theorem 6 (line 678), and
  Theorem 7 (line 713). The local text cache is omitted from the public
  repository; no numbered source propositions or definitions were found by the
  named-result search.
- README check: every named result has a controlled-status row in
  `papers/Roth82StableMatching/README.md`; all source endpoints are marked
  `formalized`.
- DAG check: `DependencyDAG.tex` marks all named source results as closed and
  renders locally to `DependencyDAG.pdf`; the Theorem 3 to Theorem 7 edge is
  solid because the arbitrary-`k` padded proof uses the formal Theorem 3
  route.
- Lean audit check: `PostPaperAudit.lean` exposes one source-numbered audit
  endpoint per final paper result, and the paper root imports it.
- Dashboard-surface check: `PaperInterface.lean` exposes a 29-row human-review
  surface, with 17 paper definition/object rows, 10 named-result rows, and 2
  source-condition assumption rows. Ignored `.review_traces` logs are
  human-review state and are not tracked clean-package validation evidence.
- Verification checks for this report pass covered the generated LLM summary
  check, status sync check, dashboard precheck, targeted paper-closeout
  repository audit, assumption-sidecar JSON parse, audit-script syntax check,
  and whitespace diff check. The existing closeout evidence also records the
  Roth Lean build, placeholder scan, stale-status scan, and DAG rendering.
- Repository audit check: the targeted paper-closeout audit reports no Roth
  closeout findings.
- Skill-update pass: no new always-loaded workflow rule was needed from this
  closeout. The durable matching-specific lessons remain covered by the
  existing matching/social-choice reference route; reusable API candidates are
  listed below instead of being forced into a risky final-pass extraction.

### Reusable Library Material

- Already extracted into `EconCSLib/Markets/Matching/Basic.lean`: assignment
  side-swap, assignment extensionality from man-side matches, completeness
  transfer across equal-cardinality sides, and stability invariance under side
  swap.
- Already extracted into `EconCSLib/Markets/Matching/DeferredAcceptance.lean`:
  DA run-prefix states, proposal-removal and proposal-monotonicity lemmas,
  finite-fold termination/stability closure, all-pairs-acceptable completeness,
  strict-preference profile predicates, the rejected-pair impossibility
  invariant, and the reusable DA men-optimality theorem.
- Remaining extraction candidates: generic direct-mechanism incentive
  predicates, Pareto/efficiency predicates for complete assignments, finite
  serial-dictatorship APIs, and rank-based report-misrepresentation predicates.
  They remain in the Roth paper namespace because their current
  names and statements are still paper-facing wrappers; moving them cleanly
  should be a separate API-design pass.

## 12. Paper Assumption Provenance
Every paper-facing theorem premise that is not derived in Lean is routed through
`Assumptions.lean` and checked separately as a paper/source model assumption.

| Assumption declaration | Lean declaration | Source location / statement | Assumption validators | Comments |
|---|---|---|---|---|
| Equal-size one-to-one marriage market | `assumption_equal_cardinality` | `Roth82StableMatching.txt`, lines 110-142 and 176-180 | codex-gpt-5.5-semantic-rejudge (model; paper_condition; 2026-06-29T18:08:26Z) | Routes the visible `hcard` premise as the paper's equal-size one-to-one marriage-problem domain, not a proof certificate. |
| Simple report ranks the obtained partner first | `assumption_simple_report_ranks_partner_first` | `Roth82StableMatching.txt`, lines 522-539 | codex-gpt-5.5-semantic-rejudge (model; paper_condition; 2026-06-29T18:08:26Z) | Routes the visible `hfirst` premise as Roth's simple-misrepresentation condition, not a proof certificate. |

### Source-Domain and Compatibility Notes

- Source-domain note: Roth Section 2 explicitly assumes complete/transitive
  strict preference relations and then says only strict preferences will be
  considered. Strict preferences are therefore not an additional Lean caveat for
  Theorems 2, 3, 4, 5, 6, 7, Corollary 5.1, or Lemma 1.
- General-matching scope note: Roth distinguishes quota/many-to-one general
  matching from the monogamous marriage problem, then states that the marriage
  problem will represent the strict-preference general problem for the paper's
  arguments. Lean follows that source route by formalizing the strict one-to-one
  marriage-problem representation; it does not separately define a quota
  matching API in this paper folder.
- Theorem 3 and Theorem 7 use `paper_strict_preference_profile`, which requires
  strict rankings over the opposite side but intentionally does not impose the
  all-pairs-acceptable encoding used by the complete marriage-domain theorems.
- Generic DA truthfulness and simple-misreport certificate APIs remain in the
  file for compatibility with arbitrary utility profiles, but the source-domain
  Lemma 2, Theorem 5, and Corollary 5.1 wrappers no longer assume those
  certificates.
- `DaNoNeedToMisrepresentFirstChoiceForWomenCertificate`: a compatibility
  certificate API for Corollary 5.1. The source strict-domain endpoint is
  closed by
  `paper_da_no_need_to_misrepresent_first_choice_for_women_on_strict_domain`.
- `DaNoProfitableFirstChoiceMisreportForWomenCertificate`: a broad
  no-profitable-false-top wrapper retained as a compatibility API. It is
  stronger than Roth's proof-language reading.

## 13. Displayed Formula Provenance
Displayed and source-defining formulas are tracked through the paper-facing rows in `PaperInterface.lean` and the current statement-match sidecars. This report pass found no standalone formula-provenance issue beyond any source notes already listed above.

## 14. Library Lift Pass
Reusable matching-market material from this formalization lives in `EconCSLib.Markets.Matching`, including deferred-acceptance invariants, stability theorems, proposer-optimality, side-swapping, and strict-marriage support. No additional extraction was needed in this report pass.

## 15. DAG Audit
`DependencyDAG.tex` and `DependencyDAG.pdf` are present. The public holistic DAG audit reports PASS for the Roth82 DAG/source/source-json comparison: the DAG exposes the stable-matching, DA, strategy, and reduction result clusters without adding or hiding theorem-level source claims.

## 16. Validation Checks

Targeted repository audit command:
`python3 scripts/audit_repository.py --paper Roth82StableMatching --paper-closeout --include-active --info-limit 0`.

<!-- BEGIN GENERATED LLM-AS-JUDGE RESULTS -->
### LLM-as-Judge Results
- Source coverage (`audit/paper_coverage_llm.json`): 29 covered.
- Statement match (`audit/statement_match_llm.json`): 29 matches.
- Lean-to-TeX translations (`audit/lean_to_tex_llm.json`): 27 row translations generated from Lean statements.
- Assumption provenance (`audit/assumption_match_llm.json`): 2 paper_condition.
- Source-record classification: no source-record classification sidecar tracked for this paper.
- Source-record structural audit (`audit/source_record_audit.json`): 29 review rows, 0 boundary inputs, 0 recursion failures.
- Review-surface audit (`audit/review_surface_llm.json`): passes over 29 review rows.
- Holistic source-first audit (`docs/AGENT_SOURCE_AUDIT.md`): PASS.
- DAG/source/source-json audit (`docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`): PASS.
<!-- END GENERATED LLM-AS-JUDGE RESULTS -->

### Statement Translation Audit

Audit date: 2026-06-29.
Scope: current 29-row dashboard surface from `PaperInterface.lean`;
`lean_to_tex_llm.json` records 27 context-free non-assumption Lean-to-TeX
drafts, `statement_match_llm.json` records paper-vs-translation judgments for
29 rows, and `assumption_match_llm.json` records the two source-condition rows.

Summary: 29 rows, 29 matches, 0 uncertain, 0 mismatch, 0 missing, 0 stale. The
serial-dictatorship mechanism is audited through
`serialDictatorshipMechanism_matches`, which spells out the permutation/match
equations rather than exposing only an opaque mechanism name.

## 17. Paper Definitions Checked
<!-- lean-derived-definitions:start -->
### Lean-Derived Dashboard Definitions

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| def preferenceProfile | `preferenceProfile` | - Roth preference profile `P`: one score table for each side. |
| def completeMarriageOutcome | `completeMarriageOutcome` | - Marriage-problem outcome: a complete one-to-one matching. |
| def stable | `stable` | - Stable matching: every assigned partner is acceptable and no man-woman pair strictly blocks the matching. |
| def strictMarriageDomain | `strictMarriageDomain` | - Strict marriage domain: each side has strict rankings over the opposite side, and every potential pair is strictly preferred to being unmatched. |
| def stableOutcomes | `stableOutcomes` | - The stable-outcome set `C(P)` for a reported preference profile. |
| def menOptimal | `menOptimal` | - A stable matching is men-optimal if every man weakly prefers it to any stable matching. |
| def womenOptimal | `womenOptimal` | - Women-optimal stable matching, with the symmetric weak-preference condition. |
| def possibleForMan | `possibleForMan` | - A woman is possible for a man if some stable outcome matches them. |
| def stableMatchingProcedure | `stableMatchingProcedure` | - Stable matching procedure on strict reported preference profiles. |
| def truthfulForAllAgents | `truthfulForAllAgents` | - Truthful revelation is dominant for both sides on strict true and reported profiles. |
| def menDeferredAcceptance | `menDeferredAcceptance` | - Men-proposing deferred acceptance, Roth's procedure/outcome `G(P)`/`g(P)`. |
| def womenDeferredAcceptance | `womenDeferredAcceptance` | - Women-proposing deferred acceptance, represented on the original `(M, W)` sides by reversing roles and swapping the resulting assignment back. |
| def paretoOptimal | `paretoOptimal` | - Pareto-optimal complete matching among complete matchings. |
| def efficientMatchingProcedure | `efficientMatchingProcedure` | - Efficient procedure: every reported preference profile returns a Pareto-optimal matching. |
| theorem serialDictatorshipMechanism_matches | `serialDictatorshipMechanism_matches` | - Serial-dictatorship mechanism chooses the permutation from the men's reported preferences and matches each man to that woman and each woman to the inverse image under the permutation. |
| def manReportStrictlyRanksPartnerFirst | `manReportStrictlyRanksPartnerFirst` | - A report strictly ranks the optional partner first. |
| def reportMisrepresentsKthChoice | `reportMisrepresentsKthChoice` | - A report changes the identity of some alternative that was truly ranked `k`. |
<!-- lean-derived-definitions:end -->

## 18. Named Theorem Statements Checked
### Theorem-by-Theorem Validation

| Paper item | Lean declaration | Status | Statement match | Notes |
|---|---|---|---|---|
| Theorem 1 (stable outcomes are nonempty) | `PaperInterface.theorem1_stable_complete_outcome_exists_on_strict_marriage_domain` | formalized | exact wrapper plus source-domain complete-outcome endpoint | DA step-invariant preservation, finite-fold termination, and the terminated-invariant stability proof are closed in `EconCSLib`. On Roth's equal-size strict marriage domain, Lean also proves the DA output is complete. |
| Theorem 2 (men- and women-optimal stable outcomes exist) | `PaperInterface.theorem2_optimal_stable_outcomes_on_strict_marriage_domain` | formalized | source strict marriage domain | The theorem is proved from a reusable DA rejected-pair invariant and role reversal. Roth explicitly assumes complete/transitive strict preferences and excludes indifference; the strict-utility/all-pairs-acceptable encoding represents the no-unmatched complete marriage model. Arbitrary-utility wrappers remain compatibility APIs. |
| Theorem 3 (no stable procedure is strategyproof for all agents) | `PaperInterface.theorem3_no_stable_truthful_procedure_on_strict_profiles` | formalized | source strict-profile counterexample route | The 3-by-3 strict profiles, stable-set enumerations `C(P) = {x,y}`, `C(P') = {y}`, `C(P'') = {x}`, stable-procedure behavior on strict reports, and manipulation contradiction are formalized. |
| Theorem 4 (efficient strategyproof procedures exist) | `PaperInterface.theorem4_serial_dictatorship_constructed` | formalized | constructed serial dictatorship on the indexed strict finite marriage domain | Lean constructs the serial-dictatorship mechanism and proves efficiency, men-truthfulness, and women-truthfulness on Roth's canonical indexed finite marriage domain `Fin n`. The fully generic existence wrapper remains a compatibility certificate API. |
| Theorem 5 (one-sided truthfulness of optimal stable procedure) | `PaperInterface.theorem5_optimal_side_truthful_on_strict_domain_of_card_eq` | formalized | source equal-size strict marriage domain | Lean formalizes Roth's reduction from arbitrary reports to strict simple reports, uses the closed Lemma 2 no-harm theorem, proves the no-new-low-proposal and unique-truthful-proposer base bridges, discharges the top-rejected-proposer later-match-time induction, and obtains the women-proposing side by role reversal. Generic certificate wrappers remain compatibility APIs outside the source-domain endpoint. |
| Corollary 5.1 | `PaperInterface.corollary5_1_no_need_to_misrepresent_first_choice` | formalized | source-faithful strict-domain endpoint in both side-optimal orientations | Closed for nonempty finite strict marriage markets. Lean exposes the source-faithful reading as "every report is weakly matched by some report preserving the true first choice", proves first-choice existence, raises that partner above an arbitrary report, proves the bad and raised DA traces are equal until the raised trace holds the true first choice, and then uses top-choice persistence to prove weak dominance. The men-under-women-proposing side is exposed by role reversal; the no-profitable-false-top certificate wrapper is stronger than the source reading and is retained only as a compatibility API. |
| Lemma 1 | `PaperInterface.lemma1_strict_simple_misrepresentation_same_partner` | formalized | strict simple-report route from Theorem 2 | Closed for Roth's source strict marriage domain, where the outcome gives the manipulator a concrete partner and the replacement report strictly ranks that partner first. The fully generic wrapper remains a compatibility certificate API. |
| Lemma 2 | `PaperInterface.lemma2_strict_simple_misrepresentation_no_men_harmed_on_strict_domain` | formalized | source strict simple-report route on equal-size strict marriage domains | Lean proves Roth's minimal first-rejection induction. A worse non-manipulator gives a first crossing at his truthful DA partner; the crossing proposer is not the manipulator under the simple-report top-partner condition; the proposer has already proposed to his own truthful partner at an earlier step; and DA rejection invariants produce an even earlier crossing, contradicting minimality. The generic certificate wrapper remains for compatibility outside the source-domain statement. |
| Theorem 6 | `PaperInterface.theorem6_weak_pareto_for_men_on_strict_marriage_domain` | formalized | source strict equal-size marriage domain | Closed for Roth's nonempty equal-size strict marriage domain. Lean proves DA completeness from equal cardinality and all-pairs acceptability, derives the last active proposal step, proves Roth's final unique-proposal observation, and derives weak Pareto. |
| Theorem 7 | `PaperInterface.theorem7_arbitrary_k_on_strict_profiles` | formalized | arbitrary `k > 1` strict-profile padded Theorem 3 family | Lean defines the general rank-based `k`th-choice misreport predicate and proves the source-facing "no stable procedure on strict profiles avoids strict-profile `k`th-choice manipulation" property for every `k > 1`. The proof pads Roth's Theorem 3 profile with strictly ranked forced dummy pairs, proves the padded manipulated reports alter rank `r + 2`, restricts padded stable outcomes back to the Theorem 3 core, and derives a profitable woman-side or man-side strict-profile manipulation for any procedure stable on strict reports. |

<!-- lean-derived-statements:start -->
### Lean-Derived Dashboard Named Statements

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| theorem theorem1_stable_complete_outcome_exists_on_strict_marriage_domain | `theorem1_stable_complete_outcome_exists_on_strict_marriage_domain` | - Theorem 1: on an equal-size strict marriage domain, a stable complete outcome exists. |
| theorem theorem2_optimal_stable_outcomes_on_strict_marriage_domain | `theorem2_optimal_stable_outcomes_on_strict_marriage_domain` | - Theorem 2: men-optimal and women-optimal stable outcomes exist on the strict marriage domain. |
| theorem theorem3_no_stable_truthful_procedure_on_strict_profiles | `theorem3_no_stable_truthful_procedure_on_strict_profiles` | - Theorem 3: on Roth's strict 3-by-3 counterexample domain, no procedure stable on strict profiles is truthful for both sides. |
| theorem theorem4_serial_dictatorship_constructed | `theorem4_serial_dictatorship_constructed` | - Theorem 4: Roth's constructed serial-dictatorship procedure is efficient on strict men-side profiles, truthful for men on that strict men-side domain, and truthful for women. |
| theorem theorem5_optimal_side_truthful_on_strict_domain_of_card_eq | `theorem5_optimal_side_truthful_on_strict_domain_of_card_eq` | - Theorem 5: side-optimal deferred-acceptance procedures are strategyproof on equal-size strict marriage domains. |
| theorem corollary5_1_no_need_to_misrepresent_first_choice | `corollary5_1_no_need_to_misrepresent_first_choice` | - Corollary 5.1: under each side-optimal DA procedure, the non-proposing side can match any report's outcome with a report preserving its true first choice. |
| theorem lemma1_strict_simple_misrepresentation_same_partner | `lemma1_strict_simple_misrepresentation_same_partner` | - Lemma 1: Roth's strict simple-misrepresentation same-partner route. |
| theorem lemma2_strict_simple_misrepresentation_no_men_harmed_on_strict_domain | `lemma2_strict_simple_misrepresentation_no_men_harmed_on_strict_domain` | - Lemma 2: a strict simple misrepresentation cannot harm any other man on the strict marriage domain. |
| theorem theorem6_weak_pareto_for_men_on_strict_marriage_domain | `theorem6_weak_pareto_for_men_on_strict_marriage_domain` | - Theorem 6: the men-optimal stable outcome is weakly Pareto optimal on the strict marriage domain. |
| theorem theorem7_arbitrary_k_on_strict_profiles | `theorem7_arbitrary_k_on_strict_profiles` | - Theorem 7: for any `k > 1`, some finite balanced strict-profile market admits a profitable stable-procedure `k`th-choice manipulation. |
<!-- lean-derived-statements:end -->

## 19. Paper-Facing Statement Validator Ledger
Current source: `papers/Roth82StableMatching/audit/statement_match_llm.json`,
refreshed 2026-06-29, plus assumption provenance in
`papers/Roth82StableMatching/audit/assumption_match_llm.json`.

| Validator surface | Result |
| --- | --- |
| Statement match | 29 rows, 29 `matches`, 0 `uncertain`, 0 `mismatch`, 0 missing or stale rows. |
| Lean-to-TeX drafts | 27 non-assumption row translations generated from Lean statements. |
| Assumption provenance | 2 `paper_condition` rows: equal-size one-to-one marriage market and simple-report first-partner condition. |
| Serial-dictatorship formula | `serialDictatorshipMechanism_matches` is a `matches` row; it spells out the mechanism's man-side and woman-side matching equations. |

The full row-level validator ledger is tracked in the JSON sidecars under
`papers/Roth82StableMatching/audit/`. Human dashboard reviews and model/agent
statement checks are separate provenance lanes; this report does not change the
human-only `human_review.reviewed_rows` counter.
