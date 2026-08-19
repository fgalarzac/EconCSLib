# Final Validation Report: LG21 Test-Optional Policies

Updated: 2026-08-02

## 1. Human Verdict

**Formalized.** The selected named-theory scope is represented by 37
paper-facing rows in [`PaperInterface.lean`](PaperInterface.lean), including
nine exact audited specification/proof pairs. Two additional audit-scope
predicates in [`Assumptions.lean`](Assumptions.lean) expose the complete local
candidate records used by Theorem 3.1. All selected conclusions are proved in
Lean.

The independent human dashboard remains at 0/37 human-facing rows, so this
technical closeout does not claim human certification or human row-level
approval. The two audit-scope predicates are machine-audit conditions rather
than dashboard rows.

## 2. Closeout Status

- Completion status: formalized
- One-sentence recap: the paper's named definitions and theoretical results are
  formalized under explicit source-equilibrium semantics, with the approved
  correction to Theorem 3.2 recorded as a source correction.
- Review surface: 37 `PaperInterface.lean` rows covering 18 named-theory source
  items and nine exact specification/proof pairs, plus two audit-scope
  convention predicates whose record fields are reviewed recursively.
- Independent human dashboard review: 0/37; no human sign-off is claimed.

## 3. Source and Scope

- Paper: *Test-optional Policies: Overcoming Strategic Behavior and
  Informational Gaps*
- Source version: [arXiv:2107.08922](https://arxiv.org/pdf/2107.08922), pinned
  in `cited publication` at SHA-256
  `11fb7a52959948847ce19d85adf97256a30c3f1575941ff6efec0e33bf908e1c`
- Lean folder: `papers/LG21TestOptionalPolicies`
- Human-facing theorem file: `papers/LG21TestOptionalPolicies/PaperInterface.lean`
- Paper assumption file: `papers/LG21TestOptionalPolicies/Assumptions.lean`
- DAG artifacts: `papers/LG21TestOptionalPolicies/docs/DependencyDAG.tex` and
  `papers/LG21TestOptionalPolicies/docs/DependencyDAG.pdf`
- Normal coverage scope: named definitions, Theorems 3.1--3.2, Lemma 4.1,
  Propositions 4.2--4.3, Definition 6, and Theorem 4.4.
- Ordinary-scope exclusions: simulations, figures, numerical examples, proof
  narration, and other prose claims that are not named theoretical statements.

## 4. Researcher Summary of Checked Results

- Definition 1 is instantiated with the paper's separate test-taking and
  score-reporting stages, feasible actions, best responses, and
  Bayesian-optimal estimates on attained positive-mass branches.
- Definitions 2--5 formalize latent-skill, observable, demographic, and
  test-blankness properties on the corresponding output laws.
- Theorem 3.1 proves the optional-reporting and report-required disclosure
  patterns and the failure of the three fairness notions.
- Theorem 3.2 proves the approved corrected target: deterministic output when a
  score is reported, arbitrary common output on the no-report or no-take branch,
  and almost-everywhere test blankness under the stated fairness condition. No
  equivalence with the literal archival wording is claimed.
- Lemma 4.1 and Propositions 4.2--4.3 establish the observed-access equilibrium
  behavior and unfairness conclusions for the three requirement protocols.
- Definition 6 and Theorem 4.4 formalize the resampling policy and prove its
  observable and demographic fairness.

## 5. Remaining Boundaries and Gaps

None in the selected named-theory scope.

## 6. Additional Assumptions Beyond Paper

- None.

The Theorem 3.1 local-recalibration condition and the Section 4 active-branch
selection semantics make the source's equilibrium reasoning operational. They
are formalizations of the source model, not extra assumptions. Null branches
are treated only up to measure zero and are not assigned convenient off-path
posteriors.

**Definition 1 alone does not state this population-level closure; the
operational equilibrium formalization makes the paper's stability reasoning
precise.**

## 7. Proof-Strategy Deviations

- Complex paper-facing conclusions are first stated as exact `Spec : Prop`
  declarations and then proved as separate theorems. This exposes the complete
  target independently of proof decomposition.
- Theorem 3.1 states local recalibration explicitly and Section 4 states the
  positive-mass active-branch selection rule explicitly.
- Gaussian conditional laws use canonical representatives, while the proved
  conclusions are almost-everywhere statements and do not depend on arbitrary
  null-fibre values.

These choices change proof organization, not the selected mathematical
conclusions.

## 8. Proof Tricks Worth Reusing

- Separate attained positive-mass branches from arbitrary versions of
  conditional laws on null events.
- State a complex paper result once as an audited proposition and prove that
  exact proposition through smaller internal lemmas.
- Keep the pre-score taking decision distinct from the post-score reporting
  decision.
- Analyze deviations using information observed by the school rather than an
  unobserved latent-skill partition of deviators.

## 9. Generalizations, Conjectures, and Extensions

The positive-mass active-branch framework is independent of most Gaussian
calculations and may be reusable for other disclosure models. Extending the
posterior calculations beyond Gaussian signals is outside this closeout.

## 10. Mathematical Typos or Other Fixes Suggested in the Source Paper

- The Theorem 3.1 no-report mixture uses below-cutoff mass, rather than the
  printed reporting mass.
- The Theorem 3.1 cutoff-existence route uses proved Gaussian lower-tail
  continuity, denominator positivity, and endpoint signs; pointwise finiteness
  alone does not justify continuity of the parameterized improper integral.
- Theorem 3.2 is formalized using deterministic reported-score output and an
  arbitrary common no-report or no-take output. Its final `demographic`
  reference is read as `observable`, consistently with the theorem's argument.
  This is the approved corrected target; equivalence with the literal archival
  statement is not claimed.
- Lemma 4.1 uses the affine inverse posterior threshold.
- Proposition 4.3 uses the unconditional precision comparison.

## 11. Paper Issues or Caveats

None. The items in Section 10 are source corrections, and the explicit
equilibrium semantics in Sections 6--7 formalize the paper's intended model.
Neither category leaves an unproved central endpoint.

## 12. Detailed Formalization Evidence

The complete configured surface has 39 rows: 37 rows in
`PaperInterface.lean` and two machine-only audit-scope predicates in
`Assumptions.lean` that expose the complete optional and report-required local
candidate records. Within the 37 paper-interface rows, 27 are source-facing
statement rows and ten expose the source model or operational conventions. The
27 source-facing rows comprise nine source statements, nine exact
`Spec : Prop` declarations, and the nine theorems proving those specifications.
The paired results are:

- Theorem 3.1 for optional reporting;
- Theorem 3.1 for reporting required after testing;
- Theorem 3.1's three fairness failures;
- Theorem 3.2 for optional reporting;
- Theorem 3.2 for reporting required after testing;
- Lemma 4.1;
- Proposition 4.2;
- Proposition 4.3; and
- Theorem 4.4.

For Lemma 4.1, Propositions 4.2--4.3, and Theorem 4.4, the selected pairs are
the four `_source_core` specification/proof pairs. Their older aggregate pairs
remain checked auxiliary strengthenings that additionally package independent
profile-nonemptiness witnesses; they receive no source-coverage credit.

Definition 1 routes use explicit feasibility, timing, response, and actual
conditional-mean contracts. No paper-facing conclusion receives credit from an
opaque placeholder proposition. Positive-mass branch guards prevent an
arbitrary null-event posterior from determining behavior.

For Theorem 3.1, local recalibration records the stability condition used by
the paper's cutoff argument. For Section 4, active-branch selection records the
paper's maximal-disclosure/unravelling behavior. Both are visible on the
paper-facing route and are operational formalizations of equilibrium, not
hidden hypotheses. The report-required route does not import the optional
post-score reporting response.

Theorem 3.2 is deliberately tied to the approved corrected statement. The Lean
surface does not assert that the literal arbitrary-randomized archival wording
is equivalent to that target.

The Section 4 routes use actual Gaussian output laws. Definition 6 constructs
the source resampling policy, including conditional synthetic-score transport,
and Theorem 4.4 proves fairness for the resulting policy.

## 13. Paper Assumption Provenance

Paper-facing premises are limited to the Gaussian signal model, access and
action rules, integrability needed for the paper's conditional expectations,
the policy class in the corrected Theorem 3.2 target, and the operational
equilibrium conditions described above. Each is exposed on the review surface
and traced to the source model or the approved source-statement correction. No
paper conclusion is accepted as a premise.

The two configured declarations from `Assumptions.lean` are scope predicates,
not theorem premises: each accepts a complete candidate record and returns
`False`, so its universal closure states that no such candidate exists. The
machine ledger categorizes them in its assumption-provenance lane because of
their source file, while the semantic judgment below records them as paper
conditions rather than additional assumptions.

<!-- BEGIN GENERATED ASSUMPTION PROVENANCE LEDGER -->
### Current Canonical Evidence
Generated from the configured source-condition surface and exact current statement digests in the canonical assumption-provenance sidecar. Model, agent, and automated checks are identified as such; no human review is inferred.

| Assumption declaration | Lean declaration | Source location / statement | Assumption validators | Comments |
| --- | --- | --- | --- | --- |
| Source convention theorem3 1 optional local candidate excluded | `source_convention_theorem3_1_optional_local_candidate_excluded` | Source location: cited publication:1044-1045. The Theorem 3.1 optional-reporting equilibrium refinement rules out every positive-mass local taking/reporting candidate whose attained branches are recalibrated by their own Bayesian posterior estimates and whose changed members strictly gain. | source condition; Agent check by Codex LG21 source-convention provenance closeout; 2026-08-01 | This declaration is an audit-scope predicate for the source's operational equilibrium stability condition. It accepts one complete positive-mass local candidate so every recursively reachable field is audited; universally closing its False result is exactly the visible paper-facing no-candidate premise. It is neither an added source assumption nor a premi... |
| Source convention theorem3 1 report required local tail candidate excluded | `source_convention_theorem3_1_report_required_local_tail_candidate_excluded` | Source location: cited publication:1577-1578. The Theorem 3.1 report-required equilibrium refinement rules out every positive-mass local pre-score taking candidate whose attained report/no-report branches are recalibrated by their own Bayesian posterior estimates and whose changed takers strictly gain. | source condition; Agent check by Codex LG21 source-convention provenance closeout; 2026-08-01 | This declaration is an audit-scope predicate for the source's operational equilibrium stability condition. It accepts one complete positive-mass local candidate so every recursively reachable field is audited; universally closing its False result is exactly the visible paper-facing no-candidate premise. It is neither an added source assumption nor a premi... |
<!-- END GENERATED ASSUMPTION PROVENANCE LEDGER -->

## 14. Displayed Formula Provenance

The posterior means, no-report mixtures, output laws, score thresholds, and
precision comparisons are derived on the reviewed surface. The corrected
no-report mass and affine threshold are stated directly rather than hidden in
proof code.

<!-- BEGIN GENERATED FORMULA PROVENANCE LEDGER -->
### Current Canonical Evidence
Rows are selected from semantic `formula` and `equation` source-kind metadata within the configured semantic source-coverage scope, never from declaration names. Coverage and statement checks remain separate evidence lanes. Active coverage mode: named theoretical statements.

| Paper formula / subclaim | Lean declaration | Provenance | Validators | Comments |
| --- | --- | --- | --- | --- |
| None | `none` | None | None | No source-map row is canonically classified as a formula or equation. |
<!-- END GENERATED FORMULA PROVENANCE LEDGER -->

## 15. Library Lift Pass

The Gaussian posterior, conditional-mean, and pushforward lemmas are candidates
for shared probability/statistics use. The equilibrium refinement remains
paper-specific. The paper-facing proof routes construct or derive the required
objects; no unresolved external certificate supports a selected conclusion.

## 16. DAG Audit

`docs/DependencyDAG.tex` records the current source-model, equilibrium,
posterior, and fairness routes and is paired with `docs/DependencyDAG.pdf`.
The DAG is a researcher navigation aid; proof acceptance depends on the Lean
dependency graph and canonical audit receipts, not on the rendered layout.

## 17. Validation Checks
<!-- BEGIN GENERATED LLM-AS-JUDGE RESULTS -->
### LLM-as-Judge Results
- Source coverage (`audit/paper_coverage_llm.json`): 16 covered, 2 corrected target covered.
- Statement match (`audit/statement_match_llm.json`): 27 exact match; resolutions: 4 approved corrected source target; source conditions: 2 source condition; diagnostics: 10 orphan/stale statement-sidecar rows excluded, 10 configured rows without unambiguous current receipts.
- Lean-to-TeX translations (`audit/lean_to_tex_llm.json`): 37 row translations generated from Lean statements; recorded translation metadata, whose independent freshness is not established by this report generator.
- Assumption provenance (`audit/assumption_match_llm.json`): 2 source condition.
- Source-record classification (`audit/source_record_match_llm.json`): 56 derived, 229 source condition, 8 recursively audited support, 12 non-propositional witness data, 83 semantic model review; recorded sidecar metadata, whose independent freshness is not established by this report generator.
- Source-record structural audit (`audit/source_record_audit.json`): 29 source-record review rows (from 39 configured review-surface rows), 14 boundary inputs, 21 conclusion dependencies, 171 recursive fields, 20 semantic-model records, 0 source-record-only unresolved conclusion dependencies, 0 recursion failures; recorded structural metadata, whose independent freshness is not established by this report generator.
- Review-surface audit (`audit/review_surface_llm.json`): review surface passed over 37 review rows; recorded review-surface metadata, whose independent freshness is not established by this report generator.
- Holistic source-first audit (`docs/AGENT_SOURCE_AUDIT.md`): status not inferred by this generator.
- DAG/source/source-json audit (`docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`): status not inferred by this generator.
<!-- END GENERATED LLM-AS-JUDGE RESULTS -->

- The ten orphan/stale statement-sidecar rows and ten rows without current
  legacy manifest receipts are archived-target diagnostics. The current
  author-approved corrected-model contract supersedes those historical lanes;
  it is current, maps every corrected-model field, and makes them nonblocking.
- The strict v11 occurrence ledger independently covers all 389 generated
  conclusion/model occurrences. Its authoritative provenance gate reports no
  finding; it does not infer source correspondence from declaration names.

- The closeout command is the focused paper build:
  `env LEAN_NUM_THREADS=1 lake build LG21TestOptionalPolicies`.
- The paper closeout audit is:
  `python3 scripts/audit_repository.py --paper LG21TestOptionalPolicies --paper-closeout --include-active --info-limit 0`.
- Statement acceptance requires current semantic statement receipts for all 37
  paper-facing rows, current provenance and recursive-field receipts for the
  two audit-scope predicates, exact proposition equality for the nine
  `Spec`/proof pairs, a current source-coverage receipt for all 18 ordinary
  named-theory source items, and no unresolved recursive premise or conclusion
  dependency.
- Independent human dashboard review remains a separate evidence lane and is
  0/37.

## 18. Paper Definitions Checked

The checked definition-level items are the Gaussian signal and access model;
Definition 1 for hidden- and observed-access protocol variants; Definitions
2--5 for the four fairness and blankness notions; and Definition 6's resampling
policy. Supporting convention rows expose the optional and report-required
positive-mass candidate and active-branch selection semantics.

## 19. Named Theorem Statements Checked

Nine theorem-level conclusions have exact audited `Spec`/proof pairs:

- Theorem 3.1, optional reporting;
- Theorem 3.1, reporting required after testing;
- Theorem 3.1, failure of all three fairness notions;
- Theorem 3.2, optional reporting under the approved corrected model;
- Theorem 3.2, report-required under the approved corrected model;
- Lemma 4.1 for all three observed-access protocols (`_source_core`);
- Proposition 4.2 for all three observed-access protocols (`_source_core`);
- Proposition 4.3 for all three observed-access protocols (`_source_core`); and
- Theorem 4.4 for all three observed-access protocols (`_source_core`).

Each proof theorem has exactly the proposition stated by its adjacent audited
specification; internal proof decomposition does not weaken the conclusion.
The four older aggregate pairs are auxiliary nonvacuity strengthenings, not
selected source-coverage rows.

## 20. Paper-Facing Statement Validator Ledger

The current paper-facing surface has 37 rows within a 39-row configured audit
surface. The generated ledger
is the authoritative row-level account of semantic statement checks, exact
statement pins, validator identity, and staleness. Independent human dashboard
review remains 0/37; model, agent, and automated receipts do not imply human
certification.

<!-- BEGIN GENERATED STATEMENT VALIDATOR LEDGER -->
### Current Canonical Evidence
Independent human dashboard review: 0/37 rows. No human row-level approval is inferred. review surface passed; Agent check by Codex LG21 targeted literal-core sidecar rebind 2026-08-02; 2026-08-02 Diagnostic-only evidence excluded from this paper-facing ledger: 10 unconfigured, stale, or ambiguous statement-sidecar rows.

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| A unit mass of students has latent skill q distributed normally, and each observed feature theta_k equals q plus feature-specific independent Gaussian noise; feature K is the optional test score. | `student_gaussian_signal_model` | No completed statement check recorded. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01; recorded translation metadata, whose independent freshness is not established by this report generator | None recorded |
| - The source action constraints and access-independence model. | `access_action_constraints_and_access_independence` | No completed statement check recorded. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01; recorded translation metadata, whose independent freshness is not established by this report generator | None recorded |
| Definition 1, instantiated for hidden-access optional reporting, requires feasible timed taking/reporting actions, stage-specific weak responses, and policy-consistent Bayesian-optimal estimates. | `definition1_hidden_access_optional_source_timed` | exact match; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01; recorded translation metadata, whose independent freshness is not established by this report generator | The source Definition 1 requires feasible actions, weak responses at both decision stages, and policy-consistent PBO estimates. The hidden-access Lean carrier has explicit timed taking/reporting response and actual public/no-report PBO equations, with the no-report equality guarded by attained mass. |
| Definition 1, instantiated for observed-access optional reporting, requires feasible source-timed actions, attained-branch weak responses, and Bayesian-optimal conditional estimates on actual positive-mass action events. | `definition1_observed_access_optional_operational_source_timed` | exact match; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01; recorded translation metadata, whose independent freshness is not established by this report generator | The source timing is take before score and optional report after score. Lean represents the observed-access optional candidate through feasible source-timed actions, a.e. attained-branch responses, and actual conditional-mean PBO equations only where the action event has positive mass. |
| Definition 1, instantiated for observed-access reporting-required-after-taking, requires feasible source-timed actions, pre-score taking responses, and Bayesian-optimal conditional estimates on actual positive-mass report and no-take events. | `definition1_observed_access_report_required_operational_source_timed` | exact match; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01; recorded translation metadata, whose independent freshness is not established by this report generator | Reporting required after taking removes the score-stage report/withhold choice. Lean exposes the pre-score taking response, actual positive-mass report and no-take PBOs, and candidate closure rather than using a generic sequential-data consistency proposition. |
| Definition 1, instantiated for reporting required given observed access, requires the feasible mandatory action and the resulting all-report and no-access Bayesian-optimal estimate equations. | `definition1_observed_access_mandatory_pbo_source_witness` | exact match; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01; recorded translation metadata, whose independent freshness is not established by this report generator | For observed access with reporting required given access, feasibility forces take-and-report. Lean constructs the access and no-access PBO outputs from the Gaussian source model rather than assuming a PBO witness. |
| - The optional protocol's source-timed positive-mass candidate. Its PBO, response, and outsider-closure obligations apply only to attained branches. | `voluntary_optional_self_enforcing_candidate` | No completed statement check recorded. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01; recorded translation metadata, whose independent freshness is not established by this report generator | None recorded |
| - The report-required protocol's source-timed positive-mass candidate. | `voluntary_report_required_self_enforcing_candidate` | No completed statement check recorded. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01; recorded translation metadata, whose independent freshness is not established by this report generator | None recorded |
| - Declared operational selection for optional reporting in Section 4. This is the branch-maximal preservation rule used by the voluntary closeout. It ranges over source-timed self-enforcing positive-mass candidates; it is not a restatement or consequence of literal static-RCD Definition 1. | `voluntary_optional_active_branch_selection` | No completed statement check recorded. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01; recorded translation metadata, whose independent freshness is not established by this report generator | None recorded |
| - Declared operational selection for report-required-after-taking in Section 4. The selected source-PBO record and candidate-side response/closure evidence are part of the rule, so action selection cannot be detached from the positive-branch conditional-mean semantics. | `voluntary_report_required_active_branch_selection` | No completed statement check recorded. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01; recorded translation metadata, whose independent freshness is not established by this report generator | None recorded |
| - Common continuous-Gaussian source parameters used by the selected voluntary Section 4 routes. | `observed_access_gaussian_source` | No completed statement check recorded. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01; recorded translation metadata, whose independent freshness is not established by this report generator | None recorded |
| - A selected optional profile with its explicit active-branch convention. | `optional_active_branch_profile` | No completed statement check recorded. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01; recorded translation metadata, whose independent freshness is not established by this report generator | None recorded |
| - A selected report-required profile, its positive-branch PBO record, and its explicit active-branch convention. | `report_required_active_branch_profile` | No completed statement check recorded. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01; recorded translation metadata, whose independent freshness is not established by this report generator | None recorded |
| Definition 2 requires equal access and no-access estimate laws conditional on the same latent skill and base-feature profile in every equilibrium. | `definition2_latent_skill_fair` | exact match; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01; recorded translation metadata, whose independent freshness is not established by this report generator | Both source and Lean require equality of access and no-access estimate laws conditional on the same latent skill and base profile in every equilibrium. |
| Definition 3 requires equal access and no-access estimate laws conditional on the same observable base-feature profile in every equilibrium. | `definition3_observable_fair` | exact match; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01; recorded translation metadata, whose independent freshness is not established by this report generator | Both source and Lean require equality of access and no-access estimate laws conditional on the same observable base-feature profile in every equilibrium. |
| Definition 4 requires the unconditional estimate laws for access and no-access students to agree in every equilibrium. | `definition4_demographic_fair` | exact match; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01; recorded translation metadata, whose independent freshness is not established by this report generator | Both source and Lean require unconditional equality of access and no-access estimate laws in every equilibrium. |
| Definition 5 says a policy is test-blank when the estimate law using only base features equals the estimate law using base features and every test value in every equilibrium. | `definition5_test_blank` | exact match; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01; recorded translation metadata, whose independent freshness is not established by this report generator | Source compares base-only and full-feature estimate laws in every equilibrium. Lean must be read as equality of the policy's output laws, not merely syntactic independence of a function from a score argument. |
| - Latent-skill fairness implies observable, then demographic, fairness. | `fairness_implication_chain` | No completed statement check recorded. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01; recorded translation metadata, whose independent freshness is not established by this report generator | None recorded |
| Theorem 3.1 says that with hidden access and Bayesian-optimal estimation, every optional-reporting equilibrium has all students take, a finite base-specific test-score reporting cutoff, and positive strategic withholding below that cutoff. | `theorem3_1_optional_reporting_source_timedSpec` | exact match; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01; recorded translation metadata, whose independent freshness is not established by this report generator | Source advertises all taking, a finite base-specific score cutoff, and positive withholding for hidden-access optional reporting. Lean's visible inputs include literal source timing, Gaussian factorization, actual PBO/best-response semantics, and no-local-candidate stability; its conclusion is all taking, cutoff a.e. on the base law, and positive withhold... |
| Theorem 3.1 says that with hidden access and Bayesian-optimal estimation, every optional-reporting equilibrium has all students take, a finite base-specific test-score reporting cutoff, and positive strategic withholding below that cutoff. | `theorem3_1_optional_reporting_source_timed` | exact match; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01; recorded translation metadata, whose independent freshness is not established by this report generator | Source advertises all taking, a finite base-specific score cutoff, and positive withholding for hidden-access optional reporting. Lean's visible inputs include literal source timing, Gaussian factorization, actual PBO/best-response semantics, and no-local-candidate stability; its conclusion is all taking, cutoff a.e. on the base law, and positive withhold... |
| Theorem 3.1 says that with hidden access, Bayesian-optimal estimation, and reporting required after testing, every equilibrium has a finite base-specific latent-skill cutoff for taking and reporting, with positive withholding below the cutoff. | `theorem3_1_report_required_source_timedSpec` | exact match; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01; recorded translation metadata, whose independent freshness is not established by this report generator | Source advertises a finite latent-skill taking cutoff and positive withholding under reporting-required-after-taking. Lean preserves the pre-score take schedule, derives the no-report mass and finite cutoff a.e., and visibly requires route-local local-tail stability plus Gaussian factorization. |
| Theorem 3.1 says that with hidden access, Bayesian-optimal estimation, and reporting required after testing, every equilibrium has a finite base-specific latent-skill cutoff for taking and reporting, with positive withholding below the cutoff. | `theorem3_1_report_required_source_timed` | exact match; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01; recorded translation metadata, whose independent freshness is not established by this report generator | Source advertises a finite latent-skill taking cutoff and positive withholding under reporting-required-after-taking. Lean preserves the pre-score take schedule, derives the no-report mass and finite cutoff a.e., and visibly requires route-local local-tail stability plus Gaussian factorization. |
| Theorem 3.1 further says the Bayesian-optimal policy satisfies none of latent-skill, observable, or demographic fairness in either requirement regime. | `theorem3_1_hidden_access_pbo_fails_all_fairness_definitionsSpec` | exact match; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01; recorded translation metadata, whose independent freshness is not established by this report generator | Source says PBO fails all three fairness definitions in both hidden-access requirement regimes. Lean uses independent optional and report-required literal equilibria and derives all three failures from their actual output laws rather than accepting a fairness gap as input. |
| Theorem 3.1 further says the Bayesian-optimal policy satisfies none of latent-skill, observable, or demographic fairness in either requirement regime. | `theorem3_1_hidden_access_pbo_fails_all_fairness_definitions` | exact match; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01; recorded translation metadata, whose independent freshness is not established by this report generator | Source says PBO fails all three fairness definitions in both hidden-access requirement regimes. Lean uses independent optional and report-required literal equilibria and derives all three failures from their actual output laws rather than accepting a fairness gap as input. |
| For every supplied optional-reporting equilibrium/fibre of the approved clarified operational model, deterministic output on the reported-score branch, an arbitrary common no-report law, source fairness, and the operational Definition 5 convention imply zero reporter mass or equality of the realized output kernel and base-only law almost everywhere. | `theorem3_2_optional_reporting_clarified_modelSpec` | exact match; approved corrected source target; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01; recorded translation metadata, whose independent freshness is not established by this report generator | The approved optional target assumes deterministic reported-score output and an arbitrary common no-report law, then proves zero reporter mass or operational output-law blankness a.e. from latent or observable fairness. It is deliberately not the archival arbitrary-randomized-policy theorem. The row proves the approved corrected target and explicitly make... |
| For every supplied optional-reporting equilibrium/fibre of the approved clarified operational model, deterministic output on the reported-score branch, an arbitrary common no-report law, source fairness, and the operational Definition 5 convention imply zero reporter mass or equality of the realized output kernel and base-only law almost everywhere. | `theorem3_2_optional_reporting_clarified_model` | exact match; approved corrected source target; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01; recorded translation metadata, whose independent freshness is not established by this report generator | The approved optional target assumes deterministic reported-score output and an arbitrary common no-report law, then proves zero reporter mass or operational output-law blankness a.e. from latent or observable fairness. It is deliberately not the archival arbitrary-randomized-policy theorem. The row proves the approved corrected target and explicitly make... |
| For every supplied report-required equilibrium/fibre of the approved clarified operational model, deterministic reported-score output, an arbitrary common no-take law, nonzero Gaussian variances, finite reporter expectations under every shifted Gaussian law, and source fairness imply zero taker mass or operational test blankness almost everywhere. | `theorem3_2_report_required_clarified_modelSpec` | exact match; approved corrected source target; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01; recorded translation metadata, whose independent freshness is not established by this report generator | The approved report-required target has deterministic reported-score output, arbitrary common no-take law, nonzero Gaussian variances, and finite shifted-Gaussian reporter expectations. It proves zero taker mass or operational test blankness a.e. under source fairness. The row proves the approved corrected target and explicitly makes no equivalence claim... |
| For every supplied report-required equilibrium/fibre of the approved clarified operational model, deterministic reported-score output, an arbitrary common no-take law, nonzero Gaussian variances, finite reporter expectations under every shifted Gaussian law, and source fairness imply zero taker mass or operational test blankness almost everywhere. | `theorem3_2_report_required_clarified_model` | exact match; approved corrected source target; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01; recorded translation metadata, whose independent freshness is not established by this report generator | The approved report-required target has deterministic reported-score output, arbitrary common no-take law, nonzero Gaussian variances, and finite shifted-Gaussian reporter expectations. It proves zero taker mass or operational test blankness a.e. under source fairness. The row proves the approved corrected target and explicitly makes no equivalence claim... |
| Lemma 4.1 says that when access is observed and access students receive Bayesian-optimal estimates, the unique equilibrium has every access student take and report under every requirement regime. | `lemma4_1_observed_access_strategy_proofness_source_coreSpec` | exact match; Agent check by Codex LG21 targeted literal-core sidecar rebind 2026-08-02; 2026-08-02. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-02; recorded translation metadata, whose independent freshness is not established by this report generator | Source states unique all-take/all-report behavior under observed access and access-side PBO. Lean keeps mandatory feasibility separate and gives independent optional/report-required selected-profile a.e. action conclusions. It deliberately does not assert arbitrary static-RCD uniqueness. |
| Lemma 4.1 says that when access is observed and access students receive Bayesian-optimal estimates, the unique equilibrium has every access student take and report under every requirement regime. | `lemma4_1_observed_access_strategy_proofness_source_core` | exact match; Agent check by Codex LG21 targeted literal-core sidecar rebind 2026-08-02; 2026-08-02. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-02; recorded translation metadata, whose independent freshness is not established by this report generator | Source states unique all-take/all-report behavior under observed access and access-side PBO. Lean keeps mandatory feasibility separate and gives independent optional/report-required selected-profile a.e. action conclusions. It deliberately does not assert arbitrary static-RCD uniqueness. |
| Proposition 4.2 says every observed-access policy that is Bayesian optimal for access students fails latent-skill fairness, regardless of its treatment of students without access. | `proposition4_2_all_observed_access_requirement_protocols_source_coreSpec` | exact match; Agent check by Codex LG21 targeted literal-core sidecar rebind 2026-08-02; 2026-08-02. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-02; recorded translation metadata, whose independent freshness is not established by this report generator | Source says any observed-access policy PBO for access students is not latent-skill fair regardless of no-access treatment. Lean treats optional, report-required, and mandatory profiles independently and uses a canonical Gaussian access PBO representative that agrees with selected actual output only a.e. |
| Proposition 4.2 says every observed-access policy that is Bayesian optimal for access students fails latent-skill fairness, regardless of its treatment of students without access. | `proposition4_2_all_observed_access_requirement_protocols_source_core` | exact match; Agent check by Codex LG21 targeted literal-core sidecar rebind 2026-08-02; 2026-08-02. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-02; recorded translation metadata, whose independent freshness is not established by this report generator | Source says any observed-access policy PBO for access students is not latent-skill fair regardless of no-access treatment. Lean treats optional, report-required, and mandatory profiles independently and uses a canonical Gaussian access PBO representative that agrees with selected actual output only a.e. |
| Proposition 4.3 says the fully Bayesian-optimal observed-access policy is neither observably nor demographically fair. | `proposition4_3_all_observed_access_requirement_protocols_source_coreSpec` | exact match; Agent check by Codex LG21 targeted literal-core sidecar rebind 2026-08-02; 2026-08-02. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-02; recorded translation metadata, whose independent freshness is not established by this report generator | Source says full PBO is neither observably nor demographically fair. Lean uses direct actual observed-access output laws for independent protocol profiles, with the demographic gap established by an unconditional Gaussian precision comparison rather than invalid mixing of conditional inequalities. |
| Proposition 4.3 says the fully Bayesian-optimal observed-access policy is neither observably nor demographically fair. | `proposition4_3_all_observed_access_requirement_protocols_source_core` | exact match; Agent check by Codex LG21 targeted literal-core sidecar rebind 2026-08-02; 2026-08-02. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-02; recorded translation metadata, whose independent freshness is not established by this report generator | Source says full PBO is neither observably nor demographically fair. Lean uses direct actual observed-access output laws for independent protocol profiles, with the demographic gap established by an unconditional Gaussian precision comparison rather than invalid mixing of conditional inequalities. |
| Definition 6 uses the Bayesian posterior mean for students with access and, for students without access, draws a synthetic test score from its base-conditioned law before applying that same posterior estimator. | `definition6_observed_access_source_derived_resampling` | exact match; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-01; recorded translation metadata, whose independent freshness is not established by this report generator | Source gives access-side posterior estimation and no-access conditional synthetic-score sampling followed by the same posterior estimator. Lean must derive the base factorization, posterior kernel, and synthetic conditional-score transport from the Gaussian source rather than accepting a kernel or law equality as input. |
| Theorem 4.4 says the observed-access resampling policy is observably and demographically fair. | `theorem4_4_all_observed_access_requirement_protocols_source_coreSpec` | exact match; Agent check by Codex LG21 targeted literal-core sidecar rebind 2026-08-02; 2026-08-02. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-02; recorded translation metadata, whose independent freshness is not established by this report generator | Source says the observed-access resampling policy is observably and demographically fair. Lean proves the Definition 6 fairness route for independent optional, report-required, and mandatory profiles using actual outputs and the source-derived resampling law, not a simultaneous profile or assumed fairness certificate. |
| Theorem 4.4 says the observed-access resampling policy is observably and demographically fair. | `theorem4_4_all_observed_access_requirement_protocols_source_core` | exact match; Agent check by Codex LG21 targeted literal-core sidecar rebind 2026-08-02; 2026-08-02. Lean translation recorded; Agent check by Codex LG21 independent semantic closeout 2026-07-31; 2026-08-02; recorded translation metadata, whose independent freshness is not established by this report generator | Source says the observed-access resampling policy is observably and demographically fair. Lean proves the Definition 6 fairness route for independent optional, report-required, and mandatory profiles using actual outputs and the source-derived resampling law, not a simultaneous profile or assumed fairness certificate. |
| The Theorem 3.1 optional-reporting equilibrium refinement rules out every positive-mass local taking/reporting candidate whose attained branches are recalibrated by their own Bayesian posterior estimates and whose changed members strictly gain. | `source_convention_theorem3_1_optional_local_candidate_excluded` | source condition; Agent check by Codex LG21 source-convention provenance closeout; 2026-08-01 | This declaration is an audit-scope predicate for the source's operational equilibrium stability condition. It accepts one complete positive-mass local candidate so every recursively reachable field is audited; universally closing its False result is exactly the visible paper-facing no-candidate premise. It is neither an added source assumption nor a premi... |
| The Theorem 3.1 report-required equilibrium refinement rules out every positive-mass local pre-score taking candidate whose attained report/no-report branches are recalibrated by their own Bayesian posterior estimates and whose changed takers strictly gain. | `source_convention_theorem3_1_report_required_local_tail_candidate_excluded` | source condition; Agent check by Codex LG21 source-convention provenance closeout; 2026-08-01 | This declaration is an audit-scope predicate for the source's operational equilibrium stability condition. It accepts one complete positive-mass local candidate so every recursively reachable field is audited; universally closing its False result is exactly the visible paper-facing no-candidate premise. It is neither an added source assumption nor a premi... |
<!-- END GENERATED STATEMENT VALIDATOR LEDGER -->

## 21. Source-Coverage Audit Ledger

The ordinary source inventory contains 18 named theoretical items. Each is
linked to its `PaperInterface.lean` review row, and each of the nine complex
results is additionally linked to an exact `Spec`/proof pair. Simulations,
figures, numerical examples, and unnamed prose claims are excluded from this
ordinary named-theory audit rather than treated as missing theorems.
The Section 4 links use the four `_source_core` pairs; the corresponding
aggregate profile-existence packages remain checked auxiliary support.

<!-- BEGIN GENERATED SOURCE COVERAGE LEDGER -->
### Current Canonical Evidence
- Coverage scope: named theoretical statements.
- Source inventory: 18 source statements from `cited publication`.
- Coverage result: 2 corrected target covered, 16 covered.
- Coverage review: coverage ledger recorded; Agent check by Codex LG21 targeted literal-core sidecar rebind 2026-08-02; 2026-08-02.
- Row-local statement checks: 18/18 linked row references have a completed canonical statement check; repeated links are counted per source row.

| Source statement | Linked Lean review rows | Coverage judgment | Row-local statement checks | Comments |
| --- | --- | --- | --- | --- |
| Definition 1, instantiated for hidden-access optional reporting, requires feasible timed taking/reporting actions, stage-specific weak responses, and policy-consistent Bayesian-optimal estimates. | `definition1_hidden_access_optional_source_timed` | covered | `definition1_hidden_access_optional_source_timed`: exact match | The source Definition 1 requires feasible actions, weak responses at both decision stages, and policy-consistent PBO estimates. The hidden-access Lean carrier has explicit timed taking/reporting response and actual public/no-report PBO equations, with the no-report equality guarded by attained mass. |
| Definition 1, instantiated for reporting required given observed access, requires the feasible mandatory action and the resulting all-report and no-access Bayesian-optimal estimate equations. | `definition1_observed_access_mandatory_pbo_source_witness` | covered | `definition1_observed_access_mandatory_pbo_source_witness`: exact match | For observed access with reporting required given access, feasibility forces take-and-report. Lean constructs the access and no-access PBO outputs from the Gaussian source model rather than assuming a PBO witness. |
| Definition 1, instantiated for observed-access optional reporting, requires feasible source-timed actions, attained-branch weak responses, and Bayesian-optimal conditional estimates on actual positive-mass action events. | `definition1_observed_access_optional_operational_source_timed` | covered | `definition1_observed_access_optional_operational_source_timed`: exact match | The source timing is take before score and optional report after score. Lean represents the observed-access optional candidate through feasible source-timed actions, a.e. attained-branch responses, and actual conditional-mean PBO equations only where the action event has positive mass. |
| Definition 1, instantiated for observed-access reporting-required-after-taking, requires feasible source-timed actions, pre-score taking responses, and Bayesian-optimal conditional estimates on actual positive-mass report and no-take events. | `definition1_observed_access_report_required_operational_source_timed` | covered | `definition1_observed_access_report_required_operational_source_timed`: exact match | Reporting required after taking removes the score-stage report/withhold choice. Lean exposes the pre-score taking response, actual positive-mass report and no-take PBOs, and candidate closure rather than using a generic sequential-data consistency proposition. |
| Definition 2 requires equal access and no-access estimate laws conditional on the same latent skill and base-feature profile in every equilibrium. | `definition2_latent_skill_fair` | covered | `definition2_latent_skill_fair`: exact match | Both source and Lean require equality of access and no-access estimate laws conditional on the same latent skill and base profile in every equilibrium. |
| Definition 3 requires equal access and no-access estimate laws conditional on the same observable base-feature profile in every equilibrium. | `definition3_observable_fair` | covered | `definition3_observable_fair`: exact match | Both source and Lean require equality of access and no-access estimate laws conditional on the same observable base-feature profile in every equilibrium. |
| Definition 4 requires the unconditional estimate laws for access and no-access students to agree in every equilibrium. | `definition4_demographic_fair` | covered | `definition4_demographic_fair`: exact match | Both source and Lean require unconditional equality of access and no-access estimate laws in every equilibrium. |
| Definition 5 says a policy is test-blank when the estimate law using only base features equals the estimate law using base features and every test value in every equilibrium. | `definition5_test_blank` | covered | `definition5_test_blank`: exact match | Source compares base-only and full-feature estimate laws in every equilibrium. Lean must be read as equality of the policy's output laws, not merely syntactic independence of a function from a score argument. |
| Definition 6 uses the Bayesian posterior mean for students with access and, for students without access, draws a synthetic test score from its base-conditioned law before applying that same posterior estimator. | `definition6_observed_access_source_derived_resampling` | covered | `definition6_observed_access_source_derived_resampling`: exact match | Source gives access-side posterior estimation and no-access conditional synthetic-score sampling followed by the same posterior estimator. Lean must derive the base factorization, posterior kernel, and synthetic conditional-score transport from the Gaussian source rather than accepting a kernel or law equality as input. |
| Lemma 4.1 says that when access is observed and access students receive Bayesian-optimal estimates, the unique equilibrium has every access student take and report under every requirement regime. | `lemma4_1_observed_access_strategy_proofness_source_core` | covered | `lemma4_1_observed_access_strategy_proofness_source_core`: exact match | Source states unique all-take/all-report behavior under observed access and access-side PBO. Lean keeps mandatory feasibility separate and gives independent optional/report-required selected-profile a.e. action conclusions. It deliberately does not assert arbitrary static-RCD uniqueness. Existence and nonvacuity strengthenings remain checked auxiliary sup... |
| Proposition 4.2 says every observed-access policy that is Bayesian optimal for access students fails latent-skill fairness, regardless of its treatment of students without access. | `proposition4_2_all_observed_access_requirement_protocols_source_core` | covered | `proposition4_2_all_observed_access_requirement_protocols_source_core`: exact match | Source says any observed-access policy PBO for access students is not latent-skill fair regardless of no-access treatment. Lean treats optional, report-required, and mandatory profiles independently and uses a canonical Gaussian access PBO representative that agrees with selected actual output only a.e. Existence and nonvacuity strengthenings remain check... |
| Proposition 4.3 says the fully Bayesian-optimal observed-access policy is neither observably nor demographically fair. | `proposition4_3_all_observed_access_requirement_protocols_source_core` | covered | `proposition4_3_all_observed_access_requirement_protocols_source_core`: exact match | Source says full PBO is neither observably nor demographically fair. Lean uses direct actual observed-access output laws for independent protocol profiles, with the demographic gap established by an unconditional Gaussian precision comparison rather than invalid mixing of conditional inequalities. Existence and nonvacuity strengthenings remain checked aux... |
| Theorem 3.1 further says the Bayesian-optimal policy satisfies none of latent-skill, observable, or demographic fairness in either requirement regime. | `theorem3_1_hidden_access_pbo_fails_all_fairness_definitions` | covered | `theorem3_1_hidden_access_pbo_fails_all_fairness_definitions`: exact match | Source says PBO fails all three fairness definitions in both hidden-access requirement regimes. Lean uses independent optional and report-required literal equilibria and derives all three failures from their actual output laws rather than accepting a fairness gap as input. |
| Theorem 3.1 says that with hidden access and Bayesian-optimal estimation, every optional-reporting equilibrium has all students take, a finite base-specific test-score reporting cutoff, and positive strategic withholding below that cutoff. | `theorem3_1_optional_reporting_source_timed` | covered | `theorem3_1_optional_reporting_source_timed`: exact match | Source advertises all taking, a finite base-specific score cutoff, and positive withholding for hidden-access optional reporting. Lean's visible inputs include literal source timing, Gaussian factorization, actual PBO/best-response semantics, and no-local-candidate stability; its conclusion is all taking, cutoff a.e. on the base law, and positive withhold... |
| Theorem 3.1 says that with hidden access, Bayesian-optimal estimation, and reporting required after testing, every equilibrium has a finite base-specific latent-skill cutoff for taking and reporting, with positive withholding below the cutoff. | `theorem3_1_report_required_source_timed` | covered | `theorem3_1_report_required_source_timed`: exact match | Source advertises a finite latent-skill taking cutoff and positive withholding under reporting-required-after-taking. Lean preserves the pre-score take schedule, derives the no-report mass and finite cutoff a.e., and visibly requires route-local local-tail stability plus Gaussian factorization. |
| Theorem 3.2 says any hidden-access estimation policy satisfying latent-skill or observable fairness is test-blank. | `theorem3_2_optional_reporting_clarified_model` | corrected target covered | `theorem3_2_optional_reporting_clarified_model`: exact match; approved corrected source target | The approved optional target assumes deterministic reported-score output and an arbitrary common no-report law, then proves zero reporter mass or operational output-law blankness a.e. from latent or observable fairness. It is deliberately not the archival arbitrary-randomized-policy theorem. |
| Theorem 3.2's hidden-access fairness-impossibility presentation also supplies the archival source statement for the approved schedule-specific report-required corrected target. | `theorem3_2_report_required_clarified_model` | corrected target covered | `theorem3_2_report_required_clarified_model`: exact match; approved corrected source target | The approved report-required target has deterministic reported-score output, arbitrary common no-take law, nonzero Gaussian variances, and finite shifted-Gaussian reporter expectations. It proves zero taker mass or operational test blankness a.e. under source fairness. |
| Theorem 4.4 says the observed-access resampling policy is observably and demographically fair. | `theorem4_4_all_observed_access_requirement_protocols_source_core` | covered | `theorem4_4_all_observed_access_requirement_protocols_source_core`: exact match | Source says the observed-access resampling policy is observably and demographically fair. Lean proves the Definition 6 fairness route for independent optional, report-required, and mandatory profiles using actual outputs and the source-derived resampling law, not a simultaneous profile or assumed fairness certificate. Existence and nonvacuity strengthenin... |
<!-- END GENERATED SOURCE COVERAGE LEDGER -->
