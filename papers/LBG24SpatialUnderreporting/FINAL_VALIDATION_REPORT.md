# Final Validation Report: LBG24 Spatial Underreporting

Updated: 2026-07-31

## 1. Human Verdict

Partially formalized. Lean checks substantial Poisson, thinning, likelihood,
and corrected Eq. (8) mathematics, but it does not derive the paper's full
Theorem 1 / Appendix Theorem 2 observation law from the printed source model.
The report identifies the exact source-model gaps; no independent human
dashboard sign-off has been recorded.

## 2. Closeout Status

- Completion status: partially formalized.
- One-sentence recap: the corrected causal constructions compile, while the
  calendar-time observation process and one-endpoint Eq. (8) bridge remain
  open.
- Lean footprint: 28,994 paper-local Lean lines; `PaperInterface.lean` has
  9,699 lines; the review surface has 24 rows.
- Independent human dashboard review: 0/24.

## 3. Source and Scope

The source is pinned as `source.txt` at SHA-256
`1190631ec27bcdbd1a067d75813538e9411ccd02fef5d10d2876348d80f5f9e5`.
The public source is the
[Nature Computational Science article](https://www.nature.com/articles/s43588-023-00572-6).
Scope includes Lemma 1, Proposition 1, Theorem 1 / Appendix Theorem 2, the
likelihood equations, and the source reporting-process semantics.

## 4. Researcher Summary of Checked Results

- Poisson and reporting-delay algebra, preprocessing minima, and regression and
  zero-inflated formulas are checked.
- A selected-start exponential waiting-tail result and corrected stationary
  Palm factorization are proved.
- Finite causal traces, fixed-cap and resampled-clock models, and a
  birth-cohort thinning theorem are constructed and checked.
- The Eq. (30) and Eq. (31) algebra repairs are formalized.

## 5. Remaining Boundaries and Gaps

The source does not derive the live-history conditional transition used in Eq.
(8), connect the corrected kernels to one source endpoint and selected start,
or establish a common across-rate physical observation model. Lemma 1 and
Proposition 1 also require a decision between birth-cohort counts and
calendar-time first-report counts plus a duration/report-path survival law.

## 6. Additional Assumptions Beyond Paper

None.

Eq. (3)'s parameter domain, positive total exposure, and zero-count convention
are treated as ordinary explicit regularity conditions. They do not close the
larger source-model boundaries in Section 5.

## 7. Proof-Strategy Deviations

Lean constructs explicit Palm, fixed-cap, and resampled-clock models rather
than inferring a conditional transition from marginal independence. These
constructions show what is sufficient, but are not claimed as derivations from
the printed source model.

## 8. Proof Tricks Worth Reusing

- Separate birth-cohort thinning from calendar-time displacement.
- Use explicit causal endpoint kernels rather than marginal-independence
  shortcuts.
- Quarantine an inconsistent legacy process interface instead of deriving
  results through vacuity.

## 9. Generalizations, Conjectures, and Extensions

A reusable two-sided stationary marked-displacement theorem would support the
calendar-time reading. A general causal stopping-endpoint kernel library would
also simplify the corrected Eq. (8) construction.

## 10. Mathematical Typos or Other Fixes Suggested in the Source Paper

Eq. (30) needs the corrected first-gap term and Eq. (31) needs reciprocal
residual normalization. These algebra repairs are checked and do not by
themselves resolve the observation-process ambiguity. The [Eq. (8)
source-correction note](docs/EQ8_SOURCE_CLARIFICATION.md) records the exact
algebraic readings and their limited effect.

## 11. Paper Issues or Caveats

The paper uses incompatible birth-cohort and calendar-time readings of the
observed count and does not state enough conditional structure for Eq. (8).
These are open source-model boundaries, so the appropriate status is partial
rather than `formalized with caveat`.

## 12. Detailed Formalization Evidence

### Source-model status detail

`partially formalized`

The Lean development contains substantial checked mathematics, but it
does not yet prove the archived paper's Theorem 1 / Appendix Theorem 2 Eq. (8)
from the printed source model.  The prior `formalized` closeout is superseded
by this source-fidelity checkpoint.

The 2026-07-30 review also retracts full source credit for Lemma 1 and
Proposition 1.  Lean now proves a cumulative-intensity **birth-cohort**
thinning process: incidents born in a window which eventually report are
retained at the displayed rate.  The source does not define `N_observed`
consistently enough to identify that count with calendar-window first reports,
which are used elsewhere in its data and simulation prose.  The source also
does not supply the conditional duration/report-path survival condition needed
to derive its displayed retention probability when lifetime may depend on
report history.

The current pinned source extraction is `source.txt`, SHA-256
`1190631ec27bcdbd1a067d75813538e9411ccd02fef5d10d2876348d80f5f9e5`.

### Checked Results

- Poisson PMF algebra, reporting-delay/first-report formulas, regression
  link algebra, zero-inflated branch algebra, and raw preprocessing minima.
- The selected-start exponential waiting-tail result for the forward Poisson
  source model.
- `theorem2_stationary_palm_source_corrected_eq8`: a positive-exposure,
  stationary/Palm corrected-model conditional factorization with a finite
  causal endpoint-density input.
- An atom-safe equality from a fixed-tag, start-weighted *resampled-clock*
  model likelihood measure to the collapsed observation law.  It preserves
  endpoint atoms but is not a pushforward theorem for the paper's one-endpoint
  source model.
- A fixed Palm-tag / one-absolute-cap special case in which every stage clock
  is a deterministic residual of the same cap, not an independently resampled
  endpoint. This is still a weighted fixed-tag likelihood construction, not a
  general source-data transport.
- A canonical finite causal-policy trace with one absolute terminal endpoint,
  plus a count-dependent competing-clock instance matching the paper's
  simulator. This is a corrected-model construction, not yet a bridge from
  the source variables or printed Conditions 1--2.
- A finite birth-cohort thinning theorem from an explicit iid eventual-report
  mark law, together with the constructed marked-process unit-window strong
  law. Neither result supplies the source duration/report-path or steady-state
  bridge by itself.
- A cumulative-intensity retained-birth process theorem. It proves the full
  nonhomogeneous rate formula for the Appendix proof's cohort interpretation,
  but is deliberately withheld from direct source-result credit.
- The Eq. (30) first-gap correction and Eq. (31) reciprocal residual
  normalization in the corrected conditional calculation.

### Open Source Obligations

1. **Eq. (8) live-policy transition law.** Printed Conditions 1--2 state
   marginal rate-independence facts but do not derive the rate-free,
   live-history conditional transition between the next report gap and the
   policy's immediate stop response. The full resampled-clock construction is
   one implementation of that transition, not the minimal source condition.
   `ConditionTwoConditionalIndependenceGap.lean` contains a finite XOR
   countermodel to the weaker marginal inference.
2. **One-endpoint source-model flow.** The paper has one absolute endpoint
   `E`, a selected start `S`, and a conditioned pre-start history `H`.  The
   current corrected construction has a fixed Palm tag and an arbitrary scalar
   `startWeight`. The new canonical trace does give one endpoint for its
   generated branch, but it supplies no selected-start/disintegration bridge
   from the paper's data. The deterministic-cap Palm theorem remains a narrow
   `S = 0`, fixed-tag special case.
3. **Across-rate and physical semantics.** The corrected construction fixes
   one rate at a time; it does not establish a common rate-indexed start/end
   policy and observed-data carrier needed for the source claim that the
   residual is independent of lambda.  It also has no incident lifetime or
   proof that the paper's `E <= t_i + T_i` constraints induce its endpoint
   kernels.
4. **Legacy process route.**
   `theorem2_poisson_process_and_condition_semantics` contains the legacy
   all-real-time `HomogeneousPoissonCountingProcessByLaw` interface, which
   has a Lean eliminator to `False`.  It is quarantined and cannot support
   paper credit.
5. **Lemma 1 and Proposition 1 scope.** The constructed marked-Poisson model
   and cumulative-intensity theorem prove a retained-birth cohort process.
   The Appendix proof uses that reading when it conditions observed counts on
   births in the same interval. The source data, simulator, and figures instead
   use calendar-time first reports. A first report in a window can come from a
   birth before that window, so the cohort theorem cannot silently establish
   the physical first-report process. The source must select the intended
   event-time semantics. It must also derive the eventual-report mark law from
   duration/report paths using an explicit conditional survival identity (or
   suitable independence); its simulator permits lifetime dependence on report
   history. Calendar-time semantics additionally require a two-sided stationary
   marked-displacement theorem.

Consequently, the archived-source derivations of Eq. (6), Eq. (7), and the
source maximum-likelihood claim remain partial where they depend on Eq. (8).

### Additional-Assumption Note

Eq. (3) leaves the parameter domain, positive-total-exposure condition, and
zero-count boundary convention implicit.  This is a routine equality/
inequality/domain convention, recorded in `status.json` as an additional
assumption note.  It is not treated as a material defect or a separate proof
campaign; the intended convention should be confirmed with the author/user
when available.

### Evidence and Handoff

- `audit/paper_statement_map.json` pins each cited source location to exact
  current-source excerpts; the semantic anchor audit passes.
- `audit/source_proof_fidelity.json` records the two algebra typos as minor
  source corrections with no status impact and the Eq. (8), legacy-process, and
  Lemma-1/Proposition-1 issues as open obligations.
- `docs/SOURCE_FIDELITY_REMEDIATION_2026-07-24.md` gives dependency order,
  forbidden shortcuts, source anchors, and acceptance conditions for repair.
- Historical LLM sidecars predate this corrected map and status.  They are
  retained as historical artifacts, not current closeout evidence.  Human
  source-to-Lean review is also incomplete (0/24).

### Return To Formalized

The archived paper can return to plain `formalized` only after a nonvacuous
source-shaped Eq. (8) model supplies or receives approval for the required
full law, identifies its residual-coordinate clocks with one source endpoint,
and proves the selected-start/history and across-rate policy bridges. It must
also establish the source Lemma 1 and Proposition 1 scopes or visibly remove
them from the claimed scope. The corrected resampled-clock likelihood equality
is Lean-checked but does not discharge those source obligations. The
paper-local remediation memo records the exact acceptance conditions.

## 13. Paper Assumption Provenance

The corrected theorems expose positive exposure, stationary/Palm, causal
endpoint-density, and mark-law conditions directly. These corrected-model
inputs remain distinct from the missing source derivations in Section 5. No
legacy inconsistent process premise receives source credit.

<!-- BEGIN GENERATED ASSUMPTION PROVENANCE LEDGER -->
### Current Canonical Evidence
Generated from the configured source-condition surface and exact current statement digests in the canonical assumption-provenance sidecar. Model, agent, and automated checks are identified as such; no human review is inferred. Diagnostic-only evidence excluded from this ledger: 4 unconfigured, stale, or ambiguous source-condition sidecar rows.

| Assumption declaration | Lean declaration | Source location / statement | Assumption validators | Comments |
| --- | --- | --- | --- | --- |
| Assumption lemma2 condition one selection | `assumption_lemma2_condition_one_selection` | Condition 1: conditional on the first jump T1=t1, S has density g(t) on [t1,T], where g is independent of lambda and of the post-T1 Poisson sample path. | source condition; Agent check by codex-gpt-5-root-lbg24-assumption-v3-closeout; 2026-07-18 | The declaration records a source model condition, theorem condition, or corrected causal endpoint framing visible in the pinned source. Premise-level checks: 1 source condition |
| Assumption theorem2 condition density source model | `assumption_theorem2_condition_density_source_model` | Condition 2: conditional on the observed jump history through t, E has an h_m(t) law independent of lambda, and conditional on T1 the distribution of E is independent of the realization of S. | source condition; Agent check by codex-gpt-5-root-lbg24-assumption-v3-closeout; 2026-07-18 | The declaration records a source model condition, theorem condition, or corrected causal endpoint framing visible in the pinned source. Premise-level checks: 1 source condition |
| Assumption lemma2 forward source model | `assumption_lemma2_forward_source_model` | Lemma 2. If the distribution of S satisfies condition 1, then the distribution of the time between any realization of S and the next jump time TX(S)+1 is an exponential random variable with rate λ. | source condition; Agent check by codex-gpt-5-lbg24-current-v10-assumption-rebind; 2026-07-28 | The source-model abbreviation packages the positive-rate homogeneous Poisson report experiment and Condition 1 selected-start convention used for Lemma 2. It does not package the exponential-tail conclusion. Premise-level checks: 1 source condition |
<!-- END GENERATED ASSUMPTION PROVENANCE LEDGER -->

## 14. Displayed Formula Provenance

The Poisson rates, waiting-tail, likelihood, Eq. (30), and Eq. (31) formulas
have checked routes. Eq. (8), and the Eq. (6)--(7) consequences that depend on
it, remain only partially connected to the archived source model.

<!-- BEGIN GENERATED FORMULA PROVENANCE LEDGER -->
### Current Canonical Evidence
Rows are selected from semantic `formula` and `equation` source-kind metadata within the configured semantic source-coverage scope, never from declaration names. Coverage and statement checks remain separate evidence lanes. Active coverage mode: named theoretical statements.

| Paper formula / subclaim | Lean declaration | Provenance | Validators | Comments |
| --- | --- | --- | --- | --- |
| None | `none` | None | None | No source-map row is canonically classified as a formula or equation. |
<!-- END GENERATED FORMULA PROVENANCE LEDGER -->

## 15. Library Lift Pass

The cumulative-intensity Poisson and marked birth-cohort theorems are reusable.
The missing stationary displacement and source-selected endpoint bridges remain
formalization opportunities, not assumptions hidden in completed rows.

## 16. DAG Audit

`docs/DependencyDAG.tex` and `docs/DependencyDAG.pdf` display the checked
Poisson and corrected-model routes separately from the open Eq. (8),
calendar-time, and across-rate bridges. The public-release check must render the
current TeX and visually inspect topology, labels, and overlap.

## 17. Validation Checks
<!-- BEGIN GENERATED LLM-AS-JUDGE RESULTS -->
### LLM-as-Judge Results
- Source coverage (`audit/paper_coverage_llm.json`): 6 covered.
- Statement match (`audit/statement_match_llm.json`): 21 exact match; source conditions: 3 source condition; diagnostics: 5 orphan/stale statement-sidecar rows excluded, 4 orphan/stale source-condition sidecar rows excluded.
- Lean-to-TeX translations (`audit/lean_to_tex_llm.json`): 23 row translations generated from Lean statements.
- Assumption provenance (`audit/assumption_match_llm.json`): 3 source condition; diagnostics: 4 unconfigured, stale, or ambiguous source-condition sidecar rows excluded.
- Source-record classification (`audit/source_record_match_llm.json`): 18 source condition, 4 recursively audited support, 11 non-propositional witness data, 5 semantic model review.
- Source-record structural audit (`audit/source_record_audit.json`): 7 source-record review rows (from 26 configured review-surface rows), 17 boundary inputs, 6 conclusion dependencies, 66 recursive fields, 7 semantic-model records, 2 source-record-only unresolved conclusion dependencies, 0 recursion failures.
- Review-surface audit (`audit/review_surface_llm.json`): review surface passed over 30 review rows.
- Holistic source-first audit (`docs/AGENT_SOURCE_AUDIT.md`): status not inferred by this generator.
- DAG/source/source-json audit (`docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`): status not inferred by this generator.
<!-- END GENERATED LLM-AS-JUDGE RESULTS -->


Focused Lean builds and source-anchor checks for the listed constructions are
recorded in the paper audit artifacts. The targeted repository command is
`python3 scripts/audit_repository.py --paper LBG24SpatialUnderreporting
--paper-closeout --include-active --info-limit 0`; a passing partial-paper audit
must preserve the open boundaries above.

## 18. Paper Definitions Checked

The checked definitions include reporting-delay and first-report models,
Poisson and retained-birth processes, causal policies, selected starts,
endpoint kernels, Palm tags, likelihood measures, and the collapsed observation
law.

## 19. Named Theorem Statements Checked

Six selected source items currently have direct coverage. Other theorem rows
are corrected-model support or explicitly partial routes; Lemma 1, Proposition
1, and the full Eq. (8)-dependent theorem chain are not reported as closed.

## 20. Paper-Facing Statement Validator Ledger

The current paper-facing surface has 24 rows. Independent human dashboard
review remains 0/24. Older generated semantic sidecars are historical evidence
only where their source and Lean identities remain current; the partial status
does not rely on relabeling them.

<!-- BEGIN GENERATED STATEMENT VALIDATOR LEDGER -->
### Current Canonical Evidence
Independent human dashboard review: 0/24 rows. No human row-level approval is inferred. review surface passed; Agent check by codex-gpt-5-lbg24-review-surface-v2-closeout; 2026-07-18 Diagnostic-only evidence excluded from this paper-facing ledger: 5 unconfigured, stale, or ambiguous statement-sidecar rows, 4 unconfigured, stale, or ambiguous source-condition sidecar rows.

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| The observed data retain incidents with at least one report, their report counts and times, and observed agency actions; Theorem 1 packages an interval realization S=s, E=e, the count in (s,e], and the report times in that interval. | `theorem2_observed_window_data_definition` | exact match; Agent check by Codex LBG24 current v10 semantic rebind; 2026-07-28. Lean translation recorded; Agent check by codex-gpt-5-lbg24-current-v10-rebind; 2026-07-28 | The source describes the observed interval data as its count/time/action representation. Lean exposes exactly the exhaustive zero, one, and multiple-report constructors for that representation, without constructing a new stochastic process. |
| Under homogeneous Poisson reporting with rate lambda_theta, the reporting delay is exponential with mean 1/lambda_theta. | `homogeneous_reporting_delay_mean_formula` | exact match; Agent check by Codex LBG24 current v10 semantic rebind; 2026-07-28. Lean translation recorded; Agent check by codex-gpt-5-lbg24-current-v10-rebind; 2026-07-28 | The source model consequence identifies a rate-lambda exponential reporting delay and mean one over lambda; Lean evaluates the same exponential expectation. |
| Equation (2) defines p(M;lambda(e-s)) as exp(-lambda(e-s))[lambda(e-s)]^M/M!. | `equation2_poisson_count_pmf_formula` | exact match; Agent check by Codex LBG24 current v10 semantic rebind; 2026-07-28. Lean translation recorded; Agent check by codex-gpt-5-lbg24-current-v10-rebind; 2026-07-28 | The source equation gives the Poisson probability mass for the count over the selected interval; Lean states the same mass formula. |
| - Homogeneous probability that an active incident receives at least one report. | `first_report_probability_formula` | exact match; Agent check by Codex LBG24 current v10 semantic rebind; 2026-07-28. Lean translation recorded; Agent check by codex-gpt-5-lbg24-current-v10-rebind; 2026-07-28 | The cited Lemma 1 derivation displays the fixed-duration probability of at least one report as one minus the exponential no-report probability; Lean isolates that same fixed-duration component. |
| which simplifies under time-homogeneity to p = 1 − �∞ 0 exp (−λθt) f(t)dt. | `lemma1_continuous_duration_first_report_probability_integral` | exact match; Agent check by Codex LBG24 current v10 semantic rebind; 2026-07-28. Lean translation recorded; Agent check by codex-gpt-5-lbg24-current-v10-rebind; 2026-07-28 | The source homogeneous specialization integrates one minus exp(-lambda t) against the duration density, which is the Lean conclusion. |
| In the simplest time-homogeneous case, this rate simplifies to: Λ′ θ = Λθ � 1 − �∞ 0 exp (−λθt) f(t)dt � . | `lemma1_continuous_duration_observed_rate_integral` | exact match; Agent check by Codex LBG24 current v10 semantic rebind; 2026-07-28. Lean translation recorded; Agent check by codex-gpt-5-lbg24-current-v10-rebind; 2026-07-28 | The source homogeneous Lemma 1 specialization gives the observed incident rate as latent rate times the duration-averaged first-report probability, exactly the reviewed formula. |
| In steady state, each unique incident gets reported with probability p = �∞ 0 Pr[m(t) ≥1\|Ti = t]f(t)dt = �∞ 0 � 1 −exp � − �t 0 λθ(u)du �� f(t)dt = 1 − �∞ 0 exp � − �t 0 λθ(u)du � f(t)dt, | `lemma1_nonhomogeneous_first_report_probability_integral` | exact match; Agent check by Codex LBG24 current v10 semantic rebind; 2026-07-28. Lean translation recorded; Agent check by codex-gpt-5-lbg24-current-v10-rebind; 2026-07-28 | The source Lemma 1 derivation gives the nonhomogeneous duration-mixture first-report probability; Lean preserves its cumulative-intensity exponential integrand. |
| Λ′ θ = Λθ � 1 − �∞ 0 exp � − �t 0 λθ(u)du � f(t)dt � . | `lemma1_nonhomogeneous_observed_rate_integral` | exact match; Agent check by Codex LBG24 current v10 semantic rebind; 2026-07-28. Lean translation recorded; Agent check by codex-gpt-5-lbg24-current-v10-rebind; 2026-07-28 | The source Lemma 1 displayed nonhomogeneous rate formula is the same latent rate times duration-mixture retention probability encoded in Lean. |
| Lemma 2 states that under Condition 1 the wait from any realization of S to the next Poisson jump is exponential with rate lambda. | `lemma2_forward_selected_start_exponential_tail` | exact match; Agent check by Codex LBG24 current v10 semantic rebind; 2026-07-28. Lean translation recorded; Agent check by codex-gpt-5-lbg24-current-v10-rebind; 2026-07-28 | The source Lemma 2 states the exponential waiting tail after a selected start under Condition 1; Lean states the same conditional no-report probability almost everywhere using a regular conditional kernel. |
| Appendix D.8.2 states that after splitting a homogeneous Poisson process at its first jump, the post-first-jump counting process remains a Poisson process with the same rate; consequently the method may start after the second report. | `appendix_shifted_poisson_after_first_jump` | exact match; Agent check by Codex LBG24 current v10 semantic rebind; 2026-07-28. Lean translation recorded; Agent check by codex-gpt-5-lbg24-current-v10-rebind; 2026-07-28 | The appendix source claim says the post-first-jump Poisson tail retains the same rate; Lean states equality almost everywhere of the conditional tail law with the exponential interarrival kernel. |
| Equation (3) gives lambda-hat_MLE=sum_i M-tilde_i / sum_i(e_i-s_i), described by the source as the maximum-likelihood estimate. | `equation3_mle_formula` | exact match; Agent check by Codex LBG24 current v10 semantic rebind; 2026-07-28. Lean translation recorded; Agent check by codex-gpt-5-lbg24-current-v10-rebind; 2026-07-28 | Equation (3) displays the total-count divided by total-exposure estimator; Lean gives that exact equality when total exposure is nonzero. |
| - Eq. (3): under the explicit positive-exposure and positive-rate convention, the displayed estimator globally maximizes the rate-dependent Poisson log-likelihood kernel. The source leaves this domain convention implicit. additional-assumption note, not a separate source defect. | `equation3_mle_global_logLikelihood_max` | exact match; Agent check by Codex LBG24 current v10 semantic rebind; 2026-07-28. Lean translation recorded; Agent check by codex-gpt-5-lbg24-current-v10-rebind; 2026-07-28 | Under the recorded positive exposure and positive rate convention, Lean proves the displayed Equation (3) estimator globally maximizes the rate-dependent Poisson log-likelihood kernel. |
| - Eq. (3) zero-count boundary: over nonnegative rates and nonnegative exposure, the displayed estimator `0` globally maximizes the rate-dependent Poisson log-likelihood kernel. | `equation3_mle_global_logLikelihood_max_zero_count` | exact match; Agent check by Codex LBG24 current v10 semantic rebind; 2026-07-28. Lean translation recorded; Agent check by codex-gpt-5-lbg24-current-v10-rebind; 2026-07-28 | Under the recorded nonnegative zero-count boundary convention, Lean proves the Equation (3) estimator zero maximizes the rate-dependent log-likelihood kernel. |
| Equations (4) and (5) are the same Poisson-regression log link lambda_theta=exp(alpha+beta^T theta). | `equation5_poisson_regression_rate_formula` | exact match; Agent check by Codex LBG24 current v10 semantic rebind; 2026-07-28. Lean translation recorded; Agent check by codex-gpt-5-lbg24-current-v10-rebind; 2026-07-28 | The source Equations (4)-(5) define the log-link rate as exp(alpha plus beta transpose theta); Lean states the same finite-coordinate expression. |
| Equation (6) substitutes the Poisson-regression rate into the incident likelihood, leaving the Poisson PMF factor up to a rate-independent proportionality factor. | `equation6_poisson_regression_likelihood_formula` | exact match; Agent check by Codex LBG24 current v10 semantic rebind; 2026-07-28. Lean translation recorded; Agent check by codex-gpt-5-lbg24-current-v10-rebind; 2026-07-28 | The source Equation (6) substitutes the log-link rate into the causal observation likelihood and factors a rate-independent residual times the Poisson count mass; Lean states that exact substitution on positive exposure. |
| The paper states that Theorem 1 extends to a zero-inflated model in which, independently for each incident, only one report can be generated with probability gamma, hence there are zero duplicate reports; Equation (7) gives the zero-duplicate and positive-duplicate likelihood branches. | `equation7_zero_inflated_likelihood_zero` | exact match; Agent check by Codex LBG24 current v10 semantic rebind; 2026-07-28. Lean translation recorded; Agent check by codex-gpt-5-lbg24-current-v10-rebind; 2026-07-28 | The source Equation (7) gives the structural-zero likelihood branch as gamma plus one-minus-gamma times the Poisson mass; Lean states that exact zero-count branch. |
| The paper states that Theorem 1 extends to a zero-inflated model in which, independently for each incident, only one report can be generated with probability gamma, hence there are zero duplicate reports; Equation (7) gives the zero-duplicate and positive-duplicate likelihood branches. | `equation7_zero_inflated_likelihood_positive_count` | exact match; Agent check by Codex LBG24 current v10 semantic rebind; 2026-07-28. Lean translation recorded; Agent check by codex-gpt-5-lbg24-current-v10-rebind; 2026-07-28 | The source Equation (7) gives the positive duplicate-count likelihood branch as one-minus-gamma times the Poisson mass; Lean states that exact branch for positive count. |
| Theorem 2: under the homogeneous Poisson report process and Conditions 1 and 2, the likelihood of the observed interval data factors as a Poisson count PMF with mean lambda(e-s) times a factor independent of lambda. | `appendix_theorem2_eq8_causal_stopping_source_model` | exact match; Agent check by Codex LBG24 current v10 semantic rebind; 2026-07-28. Lean translation recorded; Agent check by codex-gpt-5-lbg24-current-v10-rebind; 2026-07-28 | Theorem 2 factors the observed interval likelihood into a Poisson count PMF and a lambda-independent factor under the stated source conditions. Lean states the factorization for one causal realized endpoint and positive rate/exposure. |
| Equation (33) sets the NYC observation endpoint to min(S_i+100 days,t_i^INSP,t_i^WO); the surrounding text requires inspection and work-order endpoints to be stopping times. | `equation33_nyc_observation_end` | exact match; Agent check by Codex LBG24 current v10 semantic rebind; 2026-07-28. Lean translation recorded; Agent check by codex-gpt-5-lbg24-current-v10-rebind; 2026-07-28 | The source Equation (33) defines the NYC endpoint as the minimum of start plus 100 days, inspection time, and work-order time; Lean defines the same nested minimum. |
| - Eq. (33) stopping-time condition: when the first-report, inspection, and work-order times are stopping times, their 100-day min-censored endpoint is a stopping time. | `equation33_nyc_preprocessing_endpoint_is_stopping_time` | exact match; Agent check by Codex LBG24 current v10 semantic rebind; 2026-07-28. Lean translation recorded; Agent check by codex-gpt-5-lbg24-current-v10-rebind; 2026-07-28 | The source’s Equation (33) requires the constituent endpoint times to be stopping times. Lean proves the standard closure fact that their finite minimum after the 100-day shift is again a stopping time; this is proof support, not a separate empirical source claim. |
| Equation (34) sets the Chicago observation endpoint to the minimum of first-report time plus 100 days, incident closed time, and dataset retrieval/update time. | `equation34_chicago_observation_end` | exact match; Agent check by Codex LBG24 current v10 semantic rebind; 2026-07-28. Lean translation recorded; Agent check by codex-gpt-5-lbg24-current-v10-rebind; 2026-07-28 | The source Equation (34) defines the Chicago endpoint as the minimum of first report plus 100 days, closed time, and retrieval time; Lean defines the same nested minimum. |
| Condition 1: conditional on the first jump T1=t1, S has density g(t) on [t1,T], where g is independent of lambda and of the post-T1 Poisson sample path. | `assumption_lemma2_condition_one_selection` | source condition; Agent check by codex-gpt-5-root-lbg24-assumption-v3-closeout; 2026-07-18 | The declaration records a source model condition, theorem condition, or corrected causal endpoint framing visible in the pinned source. |
| Condition 2: conditional on the observed jump history through t, E has an h_m(t) law independent of lambda, and conditional on T1 the distribution of E is independent of the realization of S. | `assumption_theorem2_condition_density_source_model` | source condition; Agent check by codex-gpt-5-root-lbg24-assumption-v3-closeout; 2026-07-18 | The declaration records a source model condition, theorem condition, or corrected causal endpoint framing visible in the pinned source. |
| Lemma 2. If the distribution of S satisfies condition 1, then the distribution of the time between any realization of S and the next jump time TX(S)+1 is an exponential random variable with rate λ. | `assumption_lemma2_forward_source_model` | source condition; Agent check by codex-gpt-5-lbg24-current-v10-assumption-rebind; 2026-07-28 | The source-model abbreviation packages the positive-rate homogeneous Poisson report experiment and Condition 1 selected-start convention used for Lemma 2. It does not package the exponential-tail conclusion. |
<!-- END GENERATED STATEMENT VALIDATOR LEDGER -->

## 21. Source-Coverage Audit Ledger

The canonical named-theory selector retains six source presentations, all with
recorded coverage. Four declaration links remain after restricting navigation
to the configured semantic surface; two have exact current statement receipts.
The other raw source-map and statement-sidecar entries remain diagnostic rather
than acquiring coverage or proof credit through their storage keys.

<!-- BEGIN GENERATED SOURCE COVERAGE LEDGER -->
### Current Canonical Evidence
- Coverage scope: named theoretical statements.
- Source inventory: 6 source statements from `source.txt`.
- Coverage result: 6 covered.
- Coverage review: coverage ledger recorded; Agent check by codex-gpt-5-lbg24-v10-current-semantic-rebind; 2026-07-28.
- Row-local statement checks: 2/4 linked row references have a completed canonical statement check; repeated links are counted per source row.

| Source statement | Linked Lean review rows | Coverage judgment | Row-local statement checks | Comments |
| --- | --- | --- | --- | --- |
| Theorem 2: under the homogeneous Poisson report process and Conditions 1 and 2, the likelihood of the observed interval data factors as a Poisson count PMF with mean lambda(e-s) times a factor independent of lambda. | `appendix_theorem2_eq8_causal_stopping_source_model` | covered | `appendix_theorem2_eq8_causal_stopping_source_model`: exact match | The corrected causal Eq. (8) row proves the source likelihood factorization under a single rate-free causal endpoint policy, with one realized endpoint and an explicitly positive exposure; it does not rely on a counterfactual endpoint-clock product. |
| Lemma 1 states that independently reported incidents with a probability duration density form an observed Poisson process under steady state, with rate Lambda_theta times the duration-averaged probability of at least one report, including nonhomogeneous and homogeneous integral forms. | None recorded | covered | No linked paper-facing row recorded | The source Lemma 1 is covered by exact rows for both duration-mixture integrals and by the source-steady-state observed-process theorem, which exposes measurable path, zero, monotonicity, independent increments, and the interval Poisson law rather than a packaged certificate. 1 recorded declaration reference was outside the configured paper-facing surface... |
| Proposition 1 considers homogeneous incident and reporting Poisson processes with the Lemma 1 duration-density law, and states that the reporting rate is not identifiable from observed unique-incident counts alone; it gives the steady-state rate and a large-time observed-count limit. | None recorded | covered | No linked paper-facing row recorded | The Proposition 1 row constructs two source steady-state models with distinct reporting rates but one observed rate, and exposes both the observed-process laws and almost-sure count-average limits needed for the source non-identifiability conclusion. 1 recorded declaration reference was outside the configured paper-facing surface and is not linked here. |
| Condition 1: conditional on the first jump T1=t1, S has density g(t) on [t1,T], where g is independent of lambda and of the post-T1 Poisson sample path. | `assumption_lemma2_condition_one_selection` | covered | `assumption_lemma2_condition_one_selection`: no completed statement check | The source condition is represented as a regular conditional selection kernel: it retains the selected-start support after the first report and rate-free independence from the post-first-report tail, rather than silently treating a continuous conditional density as pointwise conditioning. |
| Condition 2: conditional on the observed jump history through t, E has an h_m(t) law independent of lambda, and conditional on T1 the distribution of E is independent of the realization of S. | `assumption_theorem2_condition_density_source_model` | covered | `assumption_theorem2_condition_density_source_model`: no completed statement check | The source condition is represented by the explicit condition-density source model: its start/end contributions are rate-free and it records the conditional endpoint selection semantics needed by the likelihood factorization. |
| Lemma 2 states that under Condition 1 the wait from any realization of S to the next Poisson jump is exponential with rate lambda. | `lemma2_forward_selected_start_exponential_tail` | covered | `lemma2_forward_selected_start_exponential_tail`: exact match | The Lemma 2 row proves the conditional no-report exponential tail from an iid exponential forward path and Condition-1 selection; the shifted-path row separately records the post-first-report iid-tail law used by that proof. |
<!-- END GENERATED SOURCE COVERAGE LEDGER -->
