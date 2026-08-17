# Final Validation Report: PKG25 No Free Lunch for Human-AI Collaboration

Updated: 2026-07-31

## 1. Human Verdict

Formalized. Lean checks the advertised forward no-free-lunch theorem and the
finite adversarial constructions behind Propositions 6, 7, and 9. Several
source conventions and local formula repairs are made explicit below; they do
not weaken the final theorem. Independent human dashboard review has not been
recorded.

## 2. Closeout Status

- Completion status: formalized.
- One-sentence recap: the calibrated raw-joint-law model and all finite witness
  constructions establish the paper's forward impossibility result.
- Lean footprint: 7,220 paper-local Lean lines; `PaperInterface.lean` has 1,026
  lines; the review surface has 50 rows.
- Independent human dashboard review: 0/50.

## 3. Source and Scope

The proceedings text is pinned as `source.txt` at SHA-256
`b4d5ad11d5f94069db886214bfcaa72eb9928c70b20585ace6238351925da2b9`.
The public source is the
[AAAI proceedings article](https://ojs.aaai.org/index.php/AAAI/article/view/33574).
The selected scope covers the calibrated prediction model, Definitions 1--4,
Propositions 6, 7, and 9, Lemma 8, and the final no-free-lunch theorem.

## 4. Researcher Summary of Checked Results

- Calibration is represented as an event identity on the raw joint law, so it
  remains meaningful on atomic and atomless prediction distributions.
- Mixtures preserve agent and strategy accuracy at the joint-law level.
- Lemma 8 and Proposition 7 construct the uniform adversarial mixture and prove
  strict underperformance against every agent.
- Proposition 9's two explicit settings and their final weighted mixture are
  checked with normalized probabilities and exact strict inequalities.

## 5. Remaining Boundaries and Gaps

None in the selected named-theory scope. Pointwise conditional probabilities on
null fibers are deliberately not claimed.

## 6. Additional Assumptions Beyond Paper

The formalization makes predictor measurability, strategy-expectation
well-formedness, finite measurable partitions, event calibration, and a zero
value on null partition cells explicit. It also states the nonempty-agent and
interior-probability domains required by the constructions. These conventions
were approved for the source model and do not weaken the final conclusion.

## 7. Proof-Strategy Deviations

Lean works with one raw joint law and event-calibration identities instead of
selecting pointwise conditional probabilities on null fibers. It proves the
mixture and partition calculations directly for the concrete finite witnesses.

## 8. Proof Tricks Worth Reusing

- Express calibration as equality of event integrals.
- Build adversarial mixtures at the joint-law level before projecting to
  accuracy formulas.
- Make every partition cell and its mass explicit in strict-gap calculations.

## 9. Generalizations, Conjectures, and Extensions

The event-calibration and finite-partition constructions can support other
human-AI collaboration impossibility results. Extending the partition route to
general measurable partitions would require additional conditional-expectation
infrastructure.

## 10. Mathematical Typos or Other Fixes Suggested in the Source Paper

The opening display is a loss rather than accuracy; Proposition 6 has a local
mixture-index typo; Proposition 9 needs `0 < epsilon < 1/2` and a denominator
normalized over both odds families. The accidental converse at a boundary
profile is not used for the advertised forward theorem.

## 11. Paper Issues or Caveats

None affecting the advertised forward theorem. The corrections and conventions
above are visible formalization notes with checked replacements.

## 12. Detailed Formalization Evidence

### Current Status

The current semantic audit supports a **formalized** status. Independent human
review has not been recorded.

The current Lean development checks the advertised forward no-free-lunch
theorem and the paper's finite adversarial proof route under a precise raw
joint-law model. It also checks the concrete strict mixtures used in
Propositions 7 and 9. The event-calibration and finite-partition/null-cell
readings below are user-approved formalization conventions, recorded visibly
as formalized notes instead of being left as hidden model choices.

The current v10 audit binds 50 source-facing `PaperInterface.lean` rows, three
independent `Assumptions.lean` rows, and 53 source-inventory items to the
frozen raw-joint-law model. It uses exact source hashes and locations plus
semantic evidence, not declaration-name matching.

### Source Pin And Anchors

- Proceedings text pin: `source.txt`
- SHA256: `b4d5ad11d5f94069db886214bfcaa72eb9928c70b20585ace6238351925da2b9`
- Canonical source anchors: `source.txt` line ranges
- Readable TeX recovery: `source_tex/sections/theorem.tex` and
  `source_tex/sections/proof.tex`
- The exact source-proof ledger is
  `audit/source_proof_fidelity.json` (schema 2).

All normative anchors below use the pinned `source.txt` line ranges. The TeX
files make stripped formulas readable, but do not replace the proceedings text
as the theorem target.

### Formalized Model

The paper's distribution is represented directly as one probability law on
`X x {0,1}`. Each predictor is a measurable `[0,1]`-valued function. The
source display
`Pr[Y=1 | P_i(X)=p] = p` at `source.txt:31-35` is formalized using the
explicit event-calibration convention

```text
E[1_{P_i(X) in A, Y=1}] = E[P_i(X) 1_{P_i(X) in A}]
```

for every measurable set `A` of reported probabilities. This is meaningful for
both atomic and atomless prediction laws. It proves the source individual
accuracy formula `E[max(P_i(X), 1-P_i(X))]` from actual joint-law classifier
accuracy.

This does not claim that a raw joint law supplies a selected pointwise
conditional probability on every null input or prediction fiber. It is the
user-approved formal reading of the paper's calibration display, not an open
proof obligation.

The paper writes an expected strategy accuracy for an arbitrary deterministic
strategy. On an arbitrary measurable space, that expectation is only a
well-defined accuracy comparison when the induced correctness indicator is
integrable. Predictor measurability and this strategy-expectation
well-formedness condition are explicit conventions in `Assumptions.lean`.
They are automatic for every finite proof witness.

The Proposition 7 and forward-theorem results use a nonempty agent domain
(`n >= 1` in the source sense): the paper takes a minimum over agents, selects
`k in [n]`, and uses the uniform weight `1/n`. Lean makes that implicit source
domain explicit through `[Nonempty (Fin n)]`. Lean also represents a strategy
as a total function on real profiles; every source-facing classifier call is
on a predictor profile in `[0,1]^n`, and Definition 4's conclusion is further
restricted to its stated interior domain.

### Partition Convention

The source's partition recipe is at `source.txt:151-156`. The checked construction is
for **finite measurable** partitions, possibly with a different finite cell
type for every agent. A positive-mass cell receives its true-label mass divided
by total cell mass; a null cell is assigned zero. Event calibration is proved
by combining equal-valued cells.

This covers every partition used in the Lemma 8 and Proposition 9 witnesses:
the exact agent-dependent cell maps are proved to yield the displayed witness
predictors under the raw finite joint-law construction. The finite measurable
scope and zero-on-null-cell totalization are the user-approved formal reading
of the paper's partition sentence and are not a remaining proof obligation.

### Checked Proof Route

### Proposition 6

The disjoint-union mixture is formalized at the full joint-law level. For every
measurable embedded input-label event, its mass is the component weight times
the original event mass. Predictor values are preserved on each component;
agent accuracy and well-formed strategy accuracy satisfy the two displayed
linear equations. This avoids an unjustified pointwise conditional-label
equality on null fibers.

### Proposition 7 And Lemma 8

Lemma 8 now returns a raw joint-law collaboration setting with the source
conclusion itself: the strategy is strictly worse than agent `k` and weakly no
better than every agent. The proof's uniform mixture step at `source.txt:180-184`
is separately checked: from a
bad interior off-half profile for every agent, the literal `1/n` mixture is a
raw setting on which the strategy is strictly worse than **every** agent.

### Proposition 9

The first auxiliary setting is checked over the full meaningful source domain
`0 < epsilon < 1/2`, not only one numerical specialization. The missing lower
bound is needed because the construction uses `epsilon` as a conditional
probability and claims interior profiles (`source.txt:280-288`).

The second auxiliary setting repairs the source's free-index denominator at
`source.txt:300-309`. The checked normalization is

```text
D = 2 + sum_j (p_j / (1 - p_j) + (1 - q_j) / q_j).
```

The final "lambda sufficiently close to one" step is no longer only
qualitative. The checked witness uses weights `7/8` for `S1` and `1/8` for
`S2`, proves the componentwise equations, and proves the resulting setting is
strictly worse than every agent (`source.txt:341-351`).

### Current Semantic Audit Findings

The 2026-07-24 source-first review expanded the raw probability laws, exact
finite partitions, and theorem conclusions rather than inferring fidelity from
Lean declaration names.

- **Raw model, Proposition 6, and Proposition 7:** passed. The joint-law
  mixture preserves measurable embedded events and both accuracy equations;
  the uniform `1/n` construction has the source's strict conclusion for every
  agent. Event calibration, predictor measurability, and strategy expectation
  definedness are visible model conditions, not theorem-facing shortcuts.
- **Lemma 8 and Proposition 9:** passed. The review expanded the actual source
  cell maps: `{0,i}` cells for Lemma 8, pooled/singleton cells for S1, and the
  center/branch-pair cells for S2. Their raw-joint partition predictors equal
  the displayed source predictors. The strict/weak conclusion shapes and the
  final `7/8`--`1/8` mixture retain the advertised conclusions.
- **Source repairs:** S1 explicitly uses `0 < epsilon < 1/2`, and S2 uses the
  normalized sum over both odds families. These repairs are visible in the
  ledger and do not weaken the checked final statements.

All cells evaluated by the Lemma 8 and Proposition 9 witness calculations
have positive mass under their interior hypotheses. The accepted zero-cell
totalization is therefore visible model scope, not an unexamined step in those
strict-gap calculations.

### Source Findings

| ID | Source location | Disposition |
| --- | --- | --- |
| `PKG25-ACCURACY-LOSS-01` | `source.txt:27-30` | Formalized note: the opening formula is loss, not accuracy. |
| `PKG25-CALIBRATION-NULL-FIBERS-01` | `source.txt:31-35` | Formalized note: event calibration is the user-approved reading of the source display. |
| `PKG25-CORRECTNESS-TIE-01` | `source.txt:104-117` | Formalized note: a strict correct/incorrect comparison needs a non-half label probability. |
| `PKG25-P6-MIXTURE-INDEX-01` | `source.txt:123-144` | Formalized note: prose says `lambda_ell`; the equations and checked mixture use `lambda_m`. |
| `PKG25-PARTITION-MEASURABLE-FINITE-01` | `source.txt:151-156` | Formalized note: finite measurable cells with zero on a null cell are the user-approved reading. |
| `PKG25-IFF-BOUNDARY-01` | `source.txt:159-172` | Formalized note: the accidental converse is refuted on boundary profiles; the advertised forward theorem is retained. |
| `PKG25-P9-S1-EPSILON-DOMAIN-01` | `source.txt:280-288` | Formalized note: use `0 < epsilon < 1/2`. |
| `PKG25-P9-S2-DENOMINATOR-01` | `source.txt:300-340` | Formalized note: repair the free-index denominator to the normalized paired-odds sum. |

The ledger gives each finding its source claim, mathematical repair obligation,
acceptance condition, and present status. Declaration names are navigation
only; they are not the audit basis.

### Audit Receipt

- Source inventory and coverage are current for all 53 items: 42 direct rows,
  three user-approved formalized-note boundaries, two support-only rows, and
  six quarantined source defects with exact semantic support.
- The 50 raw statement judgments were recorded as matches, but none currently
  binds the cached paper statement by exact semantic identity. They are
  diagnostic-only pending a content-bound reissue. The route audit still
  distinguishes theorem endpoints from source-model conventions, scoped
  construction components, proof support, and defect/refutation support.
- All three model-condition provenance judgments and all 145 source-record
  judgments are current. No current source-record item is an unresolved proof
  obligation or open semantic-model dimension.
- A 2026-07-24 run recorded passing build, conclusion-provenance, source,
  assumption, coverage, evidence-integrity, and closeout checks. That historical
  run does not establish current statement-receipt freshness.

The three formalized-note boundaries are the approved event-calibration
reading, the raw-mixture conditioning reading, and finite measurable partition
prediction with a zero value on a null cell. They are model conventions, not
weakened theorem conclusions or unresolved proof debt.

### Release State

The zero-mass conventions are logged as accepted formalization notes, and the
paper is reported as **formalized**. Independent human release certification
is not claimed.

## 13. Paper Assumption Provenance

The three configured model-condition rows expose event calibration, predictor
and strategy measurability/integrability, and finite-partition semantics. Exact
premise locations and judgments are recorded in
`audit/assumption_match_llm.json`; the theorem conclusions are derived from
those primitives.

<!-- BEGIN GENERATED ASSUMPTION PROVENANCE LEDGER -->
### Current Canonical Evidence
Generated from the configured source-condition surface and exact current statement digests in the canonical assumption-provenance sidecar. Model, agent, and automated checks are identified as such; no human review is inferred.

| Assumption declaration | Lean declaration | Source location / statement | Assumption validators | Comments |
| --- | --- | --- | --- | --- |
| Source assumption predictor measurability | `source_assumption_predictor_measurability` | Source location: source.txt:30-43; source_tex/sections/theorem.tex:2-18. Predictors must be measurable for P_i(X), calibration events, and the displayed expectations to be defined on an arbitrary measurable input space. | source condition; Agent check by Codex PKG25 independent semantic assumption audit 2026-07-24; 2026-07-24 | The source forms random reported probabilities, conditions on reported-probability events, and takes expectations under an arbitrary distribution. The unfolded condition requires each predictor P_i to be measurable, which is the standard model-definedness condition for those expressions; it neither changes the reliability conclusion nor supplies an advers... |
| Source assumption event calibration | `source_assumption_event_calibration` | Source location: source.txt:31-35; source_tex/sections/theorem.tex:6-10. For every measurable A in the reported-probability space, E[1_{P_i(X) in A,Y=1}]=E[P_i(X)1_{P_i(X) in A}] is the checked event-calibration interpretation of the source display. | source condition; Agent check by Codex PKG25 independent semantic assumption audit 2026-07-24; 2026-07-24 | The source requires calibrated predictors. Its point-fiber conditional display does not select a conditional value on a null fiber, so the reviewed model uses the explicitly documented, user-approved event identity for every measurable set of reported probabilities. This is a calibration reading of the source model, not an extra conclusion used to prove t... |
| Source assumption strategy expectation well formed | `source_assumption_strategy_expectation_well_formed` | Source location: source.txt:51-64; source_tex/sections/theorem.tex:26-34; source_tex/sections/proof.tex:26-32. The source's expected strategy accuracy requires measurability/integrability of the induced correctness indicator when C is an arbitrary deterministic function. | source condition; Agent check by Codex PKG25 independent semantic assumption audit 2026-07-24; 2026-07-24 | The source defines an arbitrary deterministic strategy and then calls its expected binary correctness an accuracy. Predictor measurability alone does not make that induced indicator integrable on an arbitrary measurable space, so the unfolded condition is the analytic definedness condition for the displayed expectation. It is discharged by the finite witn... |
<!-- END GENERATED ASSUMPTION PROVENANCE LEDGER -->

## 14. Displayed Formula Provenance

The individual and strategy accuracy formulas, mixture equations, uniform
weights, partition predictors, Proposition 9 probabilities, normalized
denominator, and final `7/8`--`1/8` mixture all have direct checked routes.

<!-- BEGIN GENERATED FORMULA PROVENANCE LEDGER -->
### Current Canonical Evidence
Rows are selected from semantic `formula` and `equation` source-kind metadata within the configured semantic source-coverage scope, never from declaration names. Coverage and statement checks remain separate evidence lanes. Scope metadata needs repair, so the full inventory is shown: paper_statement_map.json must explicitly set source_coverage_mode before a source-coverage closeout

| Paper formula / subclaim | Lean declaration | Provenance | Validators | Comments |
| --- | --- | --- | --- | --- |
| The opening display E[\|Yhat(X)-Y\|] is expected 0-1 loss, not accuracy; expected correctness is one minus this quantity. | None recorded | support only. No linked paper-facing row recorded | support only; Agent check by Codex PKG25 source-first semantic coverage review 2026-07-24; 2026-07-24 | The support theorem states for every binary prediction and label-one probability that expected correctness equals one minus 0-1 loss. That is the precise correction of the opening display's mistaken accuracy label, so the printed formula is quarantined rather than counted as a proved source claim. |
| The paper writes Pr[Y=1 \| P(X)=p]=p for each reported prediction value p. | `source_formula_probability_calibration`<br>`source_assumption_event_calibration` | conditional boundary. `source_formula_probability_calibration`: no completed statement check<br>`source_assumption_event_calibration`: no completed statement check | conditional boundary; Agent check by Codex PKG25 source-first semantic coverage review 2026-07-24; 2026-07-24 | The source prints a point-conditioned equation. The checked model instead quantifies every measurable reported-probability event and equates its label-one mass with the prediction-weighted mass, which is the user-approved event-calibration reading and deliberately does not choose a conditional probability on a null fiber. |
| Agent i's accuracy is E[max{P_i(X),1-P_i(X)}]. | `source_formula_probability_agent_accuracy` | covered. `source_formula_probability_agent_accuracy`: no completed statement check | covered; Agent check by Codex PKG25 source-first semantic coverage review 2026-07-24; 2026-07-24 | The theorem proves that each agent's accuracy in the raw joint-law setting is the joint integral of max(P_i(x), 1-P_i(x)). This is the displayed individual-accuracy formula, derived from calibration rather than assumed pointwise. |
| The induced classifier maps x to C(P_1(x),...,P_n(x)). | `source_formula_probability_strategy_classifier` | covered. `source_formula_probability_strategy_classifier`: no completed statement check | covered; Agent check by Codex PKG25 source-first semantic coverage review 2026-07-24; 2026-07-24 | The reviewed equality evaluates the strategy classifier at x by passing the full function i \|-> P_i(x) to C. This is the source formula C(P_1(x), ..., P_n(x)). |
| The mixture scales component m's joint mass by lambda_m. | `source_formula_mixture_components` | covered. `source_formula_mixture_components`: no completed statement check | covered; Agent check by Codex PKG25 source-first semantic coverage review 2026-07-24; 2026-07-24 | For every component r and measurable embedded joint event A, the reviewed theorem gives mixed mass ENNReal.ofReal(w r) times that component's mass. This is the full-joint-law version of the source mass scaling formula. |
| The mixture retains the component conditional label probability at (m,x). | `source_formula_mixture_components` | conditional boundary. `source_formula_mixture_components`: no completed statement check | conditional boundary; Agent check by Codex PKG25 source-first semantic coverage review 2026-07-24; 2026-07-24 | The source wording selects a conditional label probability at each (m,x). The checked theorem instead preserves every embedded joint event and predictor value under mixing; this is the explicit raw-law replacement when a pointwise conditional version is not selected on null fibers. |
| Each mixed predictor at (m,x) equals its component predictor P_{i,m}(x). | `source_formula_mixture_components` | covered. `source_formula_mixture_components`: no completed statement check | covered; Agent check by Codex PKG25 source-first semantic coverage review 2026-07-24; 2026-07-24 | The second conjunct of the reviewed mixture theorem states that the mixed predictor at tagged input (r,x) is exactly the r-th component predictor at x. This is the source predictor formula. |
| The source says a partition cell A induces P_i(x)=Pr[Y=1 \| X in A] for x in A. | `source_formula_probability_partition_induced_predictor` | conditional boundary. `source_formula_probability_partition_induced_predictor`: no completed statement check | conditional boundary; Agent check by Codex PKG25 source-first semantic coverage review 2026-07-24; 2026-07-24 | The linked theorem establishes the printed positive-cell quotient under an explicit positive-mass premise. The separate null-cell, event-calibration, and setting rows implement the documented finite-partition reading, but do not separately claim the printed positive-cell formula. This remains the user-approved finite-partition boundary rather than a claim... |
| A uniform mixture of the n Lemma 8 settings makes the strategy strictly less accurate than every agent. | `source_proposition7_uniform_mixture_strict_counterexample` | covered. `source_proposition7_uniform_mixture_strict_counterexample`: no completed statement check | covered; Agent check by Codex PKG25 source-first semantic coverage review 2026-07-24; 2026-07-24 | Under failure of every fixed deferral choice, the reviewed theorem constructs one setting whose strategy accuracy is strictly below every agent accuracy. This is the uniform Lemma 8 mixture contradiction used in Proposition 7. |
| At point 0 the conditional label probability is 1-C(p), while at each agent point it is C(p). | `source_formula_lemma8_labels_and_predictions` | covered. `source_formula_lemma8_labels_and_predictions`: no completed statement check | covered; Agent check by Codex PKG25 source-first semantic coverage review 2026-07-24; 2026-07-24 | The reviewed table states that the center label probability is the complement of C(p) and every agent point has label probability C(p). This is the source label assignment for Lemma 8. |
| When C(p)=0, point 0 has normalized unit mass and point i has normalized odds (1-p_i)/p_i. | `source_formula_lemma8_masses` | covered. `source_formula_lemma8_masses`: no completed statement check | covered; Agent check by Codex PKG25 source-first semantic coverage review 2026-07-24; 2026-07-24 | The mass theorem gives the false-output odds (1-p_i)/p_i, the unit center numerator, the per-agent normalized numerator, and their common denominator. These are the source C(p)=0 masses. |
| When C(p)=1, point 0 has normalized unit mass and point i has normalized odds p_i/(1-p_i). | `source_formula_lemma8_masses` | covered. `source_formula_lemma8_masses`: no completed statement check | covered; Agent check by Codex PKG25 source-first semantic coverage review 2026-07-24; 2026-07-24 | The same mass theorem gives the true-output odds p_i/(1-p_i), the unit center numerator, the per-agent normalized numerator, and their common denominator. These are the source C(p)=1 masses. |
| For each i, the {0,i} cell has conditional label probability p_i, making the constructed predictor calibrated. | `source_lemma8_partition_realization`<br>`source_lemma8_witness_calibrated` | covered. `source_lemma8_partition_realization`: no completed statement check<br>`source_lemma8_witness_calibrated`: no completed statement check | covered; Agent check by Codex PKG25 source-first semantic coverage review 2026-07-24; 2026-07-24 | The partition-realization theorem identifies every source cell predictor with the displayed Part1 prediction, and the calibration theorem gives the label-mass equals prediction times event-mass equation for every reported value. This covers the {0,i} cell calibration claim. |
| At point 0 the vector of constructed predictions is exactly the bad profile p. | `source_formula_lemma8_labels_and_predictions` | covered. `source_formula_lemma8_labels_and_predictions`: no completed statement check | covered; Agent check by Codex PKG25 source-first semantic coverage review 2026-07-24; 2026-07-24 | At the center point none, the reviewed prediction table states part1Pred b p i none = p i for every i. Thus the entire center profile is exactly the bad tuple p. |
| S1 has masses 1/3 and 2/3, conditional label probabilities epsilon and 1-epsilon, and the displayed pooled agent-k prediction. | `source_formula_proposition9_s1_family`<br>`source_proposition9_s1_partition_realization` | covered. `source_formula_proposition9_s1_family`: no completed statement check<br>`source_proposition9_s1_partition_realization`: no completed statement check | covered; Agent check by Codex PKG25 source-first semantic coverage review 2026-07-24; 2026-07-24 | The S1 family theorem gives masses 1/3 and 2/3, label probabilities epsilon and 1-epsilon, and the pooled k prediction 2/3-epsilon/3. The realization theorem connects that finite setting to the exact source partition cells. |
| In S1, agent k uses the pooled prediction 2/3-epsilon/3 at both points, every other agent uses the corresponding conditional label probability, and the resulting finite prediction cells are calibrated. | `source_formula_proposition9_s1_family`<br>`source_proposition9_s1_partition_realization` | covered. `source_formula_proposition9_s1_family`: no completed statement check<br>`source_proposition9_s1_partition_realization`: no completed statement check | covered; Agent check by Codex PKG25 source-first semantic coverage review 2026-07-24; 2026-07-24 | The S1 family theorem gives the k and non-k prediction table and a positive-cell calibration equation for every agent and reported value. The partition-realization theorem then proves the finite source cell map produces those predictors, covering the source finite-witness calibration formula. |
| In S1, agent k and C have accuracy 2/3-epsilon/3, while all other agents have accuracy 1-epsilon and are strictly more accurate for 0 < epsilon < 1/2. | `source_proposition9_s1_parameterized_accuracy_gap` | covered. `source_proposition9_s1_parameterized_accuracy_gap`: no completed statement check | covered; Agent check by Codex PKG25 source-first semantic coverage review 2026-07-24; 2026-07-24 | Under 0 < epsilon < 1/2 and off-half deferral, the reviewed theorem gives C and k accuracy 2/3-epsilon/3, every other agent accuracy 1-epsilon, and the strict inequality. This is the source S1 accuracy calculation. |
| The printed S2 masses contain a free-index q-odds term in their common denominator and therefore do not literally specify one normalized distribution. | None recorded | support only. No linked paper-facing row recorded | support only; Agent check by Codex PKG25 source-first semantic coverage review 2026-07-24; 2026-07-24 | The support theorem fixes one denominator D as 2 plus the finite sum of both p-odds and q-odds terms. This exact repaired expression refutes the printed free-index denominator, which cannot define one normalized S2 distribution. |
| The repaired S2 law uses D=2+sum_j(p_j/(1-p_j)+(1-q_j)/q_j), then the displayed p-copy and q-copy normalized masses and labels. | `source_formula_proposition9_s2_repaired_normalizer`<br>`source_proposition9_s2_repaired_mass_normalized`<br>`source_formula_proposition9_s2_construction` | covered. `source_formula_proposition9_s2_repaired_normalizer`: no completed statement check<br>`source_proposition9_s2_repaired_mass_normalized`: no completed statement check<br>`source_formula_proposition9_s2_construction`: no completed statement check | covered; Agent check by Codex PKG25 source-first semantic coverage review 2026-07-24; 2026-07-24 | The linked rows state the repaired single denominator, prove the finite S2 mass function sums to one under interiority, and give the two copy weights, masses, labels, and predictions. This is explicitly the checked repair rather than a claim that the printed formula was valid. |
| The paired cells in copy 0 have conditional label probability p_i and those in copy 1 have conditional label probability q_i. | `source_proposition9_s2_partition_realization`<br>`source_proposition9_s2_calibrated` | covered. `source_proposition9_s2_partition_realization`: no completed statement check<br>`source_proposition9_s2_calibrated`: no completed statement check | covered; Agent check by Codex PKG25 source-first semantic coverage review 2026-07-24; 2026-07-24 | The realization theorem equates each finite source-cell predictor to the displayed S2 predictor, and the calibration theorem gives the event label-mass equation for every agent and reported value. This covers the p-copy and q-copy cell calibration equations of the repaired law. |
| Mixing S1 with weight lambda and S2 with weight 1-lambda preserves the componentwise accuracy equations; a lambda close enough to one makes every agent strictly beat C. | `source_formula_proposition9_explicit_final_mixture`<br>`source_proposition9_explicit_final_mixture_strict_counterexample` | covered. `source_formula_proposition9_explicit_final_mixture`: no completed statement check<br>`source_proposition9_explicit_final_mixture_strict_counterexample`: no completed statement check | covered; Agent check by Codex PKG25 source-first semantic coverage review 2026-07-24; 2026-07-24 | One theorem supplies the exact 7/8 and 1/8 componentwise accuracy equations, and the other constructs a mixed setting where C is strictly below every agent from the S2 half-slice hypotheses. These are the checked explicit-weight form of the source final-mixture argument. |
<!-- END GENERATED FORMULA PROVENANCE LEDGER -->

## 15. Library Lift Pass

The event-calibration, raw-law mixture, and finite-partition components are
reusable probability infrastructure. No unresolved library certificate remains
on a paper-facing theorem.

## 16. DAG Audit

`docs/DependencyDAG.tex` and `docs/DependencyDAG.pdf` show the calibrated model,
mixture and partition constructions, Propositions 6--9, Lemma 8, and the final
theorem. The rendered graph is part of the release visual check for readable
labels, topology, and nonoverlap.

## 17. Validation Checks
<!-- BEGIN GENERATED LLM-AS-JUDGE RESULTS -->
### LLM-as-Judge Results
- Source coverage (`audit/paper_coverage_llm.json`): 42 covered, 8 support only, 3 formalization boundary; diagnostics: full inventory shown because paper_statement_map.json must explicitly set source_coverage_mode before a source-coverage closeout.
- Statement match (`audit/statement_match_llm.json`): no rows; source conditions: 3 source condition; diagnostics: 50 orphan/stale statement-sidecar rows excluded, 50 configured rows without unambiguous current receipts.
- Lean-to-TeX translations (`audit/lean_to_tex_llm.json`): 50 row translations generated from Lean statements.
- Assumption provenance (`audit/assumption_match_llm.json`): 3 source condition.
- Source-record classification (`audit/source_record_match_llm.json`): 85 source condition, 7 non-propositional witness data, 53 semantic model review.
- Source-record structural audit (`audit/source_record_audit.json`): 53 source-record review rows, 76 boundary inputs, 24 conclusion dependencies, 16 recursive fields, 53 semantic-model records, 0 source-record-only unresolved conclusion dependencies, 0 recursion failures.
- Review-surface audit (`audit/review_surface_llm.json`): review surface passed over 53 review rows.
- Holistic source-first audit (`docs/AGENT_SOURCE_AUDIT.md`): status not inferred by this generator.
- DAG/source/source-json audit (`docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`): status not inferred by this generator.
<!-- END GENERATED LLM-AS-JUDGE RESULTS -->


The focused paper build, conclusion-provenance check, source and premise
reviews, recursive-model audit, and strict paper closeout passed on the current
surface. The targeted command is `python3 scripts/audit_repository.py --paper
PKG25NoFreeLunch --paper-closeout --include-active --info-limit 0`.

## 18. Paper Definitions Checked

The checked definitions cover calibrated predictors, individual and strategy
accuracy, collaboration settings, partitions, mixtures, and the source's
forward impossibility property.

## 19. Named Theorem Statements Checked

Propositions 6, 7, and 9, Lemma 8, and the forward no-free-lunch theorem have
direct paper-facing conclusions. The boundary-profile converse is recorded as
false and is not used as theorem evidence.

## 20. Paper-Facing Statement Validator Ledger

The configured semantic surface contains 53 rows: 50 statements and three
source conditions. The three condition receipts bind exactly, while none of the
50 raw statement receipts does; those statement rows remain diagnostic-only.
Independent human dashboard review remains 0/50.

<!-- BEGIN GENERATED STATEMENT VALIDATOR LEDGER -->
### Current Canonical Evidence
Independent human dashboard review: 0/50 rows. No human row-level approval is inferred. review surface passed; Agent check by Codex PKG25 independent semantic review-surface audit 2026-07-24; 2026-07-24 Diagnostic-only evidence excluded from this paper-facing ledger: 50 unconfigured, stale, or ambiguous statement-sidecar rows.

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| The opening display E[\|Yhat(X)-Y\|] is expected 0-1 loss, not accuracy; expected correctness is one minus this quantity. | `source_accuracy_loss_correction` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| A collaboration setting is a probability distribution over inputs and binary labels together with n calibrated predictors. | `source_definition_probability_collaboration_setting` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| A predictor maps inputs to probabilities in [0,1]. | `source_formula_probability_predictor_range` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| For every measurable A in the reported-probability space, E[1_{P_i(X) in A,Y=1}]=E[P_i(X)1_{P_i(X) in A}] is the checked event-calibration interpretation of the source display. | `source_formula_probability_calibration` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| Agent i's induced classifier rounds P_i(x), with round(1/2)=1. | `source_definition_rounding_convention` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| Agent i's induced classifier rounds P_i(x), with round(1/2)=1. | `source_formula_probability_agent_classifier` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| Agent i's accuracy is E[max{P_i(X),1-P_i(X)}]. | `source_formula_probability_agent_accuracy` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| A collaboration strategy maps n reported probabilities to a binary label. | `source_definition_collaboration_strategy` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| The induced classifier maps x to C(P_1(x),...,P_n(x)). | `source_formula_probability_strategy_classifier` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| a_C(S) is expected binary correctness of the collaboration classifier on setting S. | `source_formula_probability_strategy_accuracy` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| For a finite measurable partition, a positive-mass cell receives its true-label mass divided by cell mass; a null cell is explicitly assigned 0, and the resulting predictor is event-calibrated. | `source_formula_probability_partition_induced_predictor` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| For a finite measurable partition, a positive-mass cell receives its true-label mass divided by cell mass; a null cell is explicitly assigned 0, and the resulting predictor is event-calibrated. | `source_convention_probability_partition_zero_mass_prediction` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| For a finite measurable partition, a positive-mass cell receives its true-label mass divided by cell mass; a null cell is explicitly assigned 0, and the resulting predictor is event-calibrated. | `source_probability_partition_predictor_calibrated_events` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| For a finite measurable partition, a positive-mass cell receives its true-label mass divided by cell mass; a null cell is explicitly assigned 0, and the resulting predictor is event-calibrated. | `source_probability_partition_collaboration_setting` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| The source's min over i in [n] and its existential fixed agent require n to be nonzero. | `source_formula_reliable_probability_iff` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| - The finite embedding preserves each individual agent's exact accuracy. | `source_finite_embedding_preserves_agent_accuracy` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| - The finite embedding preserves the collaboration strategy's exact accuracy. | `source_finite_embedding_preserves_strategy_accuracy` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| - General source reliability therefore implies reliability on every checked witness. | `source_bridge_probability_reliability_to_finite` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| On every interior profile, C follows one fixed agent away from p_k=1/2 and returns one fixed label on the p_k=1/2 slice. | `source_formula_interior_prediction_profile_iff` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| On every interior profile, C follows one fixed agent away from p_k=1/2 and returns one fixed label on the p_k=1/2 slice. | `source_formula_non_collaborative_iff` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| A prediction is correct at x when it equals the rounded conditional label probability at x. | `source_formula_correct_on_iff` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| A prediction is incorrect at x when it differs from the rounded conditional label probability at x. | `source_formula_incorrect_on_iff` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| Two agents or strategies agree at x when their binary predictions are equal. | `source_formula_agree_on_iff` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| Two agents or strategies disagree at x when their binary predictions differ. | `source_formula_disagree_on_iff` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| The source claims that one positive-mass point where i is correct and j incorrect makes the accuracy comparison strict; this fails at a half tie under the stated rounding convention. | `source_correctness_strict_gap_half_tie_counterexample` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| The source claims that one positive-mass point where i is correct and j incorrect makes the accuracy comparison strict; this fails at a half tie under the stated rounding convention. | `source_correctness_strict_gap_corrected` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| Each mixed predictor at (m,x) equals its component predictor P_{i,m}(x). | `source_formula_mixture_components` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| The Proposition 6 prose says to sample m with probability lambda_ell after the displayed component equations use lambda_m. | `source_proposition6_linear_combination_settings` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| Every reliable collaboration strategy is non-collaborative. | `source_theorem1_no_free_lunch` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| The proof section restates reliability iff non-collaboration, but Definition 4 leaves boundary behavior unconstrained, so only the forward implication is valid. | `source_iff_converse_boundary_counterexample` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| Reliability forces one fixed agent k followed at every interior profile with p_k not equal to 1/2. | `source_proposition7_reliability_forces_fixed_deferral` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| A uniform mixture of the n Lemma 8 settings makes the strategy strictly less accurate than every agent. | `source_proposition7_uniform_mixture_strict_counterexample` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| The normalized odds make the center mass at least each paired point mass, strictly for the bad non-half coordinate, yielding the weak and strict accuracy inequalities. | `source_lemma8_bad_tuple_counterexample_setting` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| When C(p)=1, point 0 has normalized unit mass and point i has normalized odds p_i/(1-p_i). | `source_formula_lemma8_masses` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| At point 0 the vector of constructed predictions is exactly the bad profile p. | `source_formula_lemma8_labels_and_predictions` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| For each i, the {0,i} cell has conditional label probability p_i, making the constructed predictor calibrated. | `source_lemma8_partition_realization` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| For each i, the {0,i} cell has conditional label probability p_i, making the constructed predictor calibrated. | `source_lemma8_witness_calibrated` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| In S1, agent k uses the pooled prediction 2/3-epsilon/3 at both points, every other agent uses the corresponding conditional label probability, and the resulting finite prediction cells are calibrated. | `source_formula_proposition9_s1_family` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| The S1 construction requires 0 < epsilon < 1/2 because it uses epsilon and 1-epsilon as probabilities and its profiles as elements of (0,1)^n, although the source prints only epsilon < 1/2. | `source_proposition9_s1_positive_parameter_validity` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| In S1, agent k uses the pooled prediction 2/3-epsilon/3 at both points, every other agent uses the corresponding conditional label probability, and the resulting finite prediction cells are calibrated. | `source_proposition9_s1_partition_realization` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| In S1, agent k and C have accuracy 2/3-epsilon/3, while all other agents have accuracy 1-epsilon and are strictly more accurate for 0 < epsilon < 1/2. | `source_proposition9_s1_parameterized_accuracy_gap` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| The repaired S2 law uses D=2+sum_j(p_j/(1-p_j)+(1-q_j)/q_j), then the displayed p-copy and q-copy normalized masses and labels. | `source_formula_proposition9_s2_repaired_normalizer` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| The repaired S2 law uses D=2+sum_j(p_j/(1-p_j)+(1-q_j)/q_j), then the displayed p-copy and q-copy normalized masses and labels. | `source_proposition9_s2_repaired_mass_normalized` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| The repaired S2 law uses D=2+sum_j(p_j/(1-p_j)+(1-q_j)/q_j), then the displayed p-copy and q-copy normalized masses and labels. | `source_formula_proposition9_s2_construction` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| The paired cells in copy 0 have conditional label probability p_i and those in copy 1 have conditional label probability q_i. | `source_proposition9_s2_partition_realization` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| The paired cells in copy 0 have conditional label probability p_i and those in copy 1 have conditional label probability q_i. | `source_proposition9_s2_calibrated` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| The two center predictor profiles equal p and q; C is wrong at both centers while k is correct at one, so C is strictly less accurate than k. | `source_proposition9_s2_strict_gap` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| Given fixed off-half deferral to k, reliability forces one fixed output alpha on every interior p_k=1/2 profile. | `source_proposition9_reliability_forces_fixed_tie_label` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| Mixing S1 with weight lambda and S2 with weight 1-lambda preserves the componentwise accuracy equations; a lambda close enough to one makes every agent strictly beat C. | `source_formula_proposition9_explicit_final_mixture` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| Mixing S1 with weight lambda and S2 with weight 1-lambda preserves the componentwise accuracy equations; a lambda close enough to one makes every agent strictly beat C. | `source_proposition9_explicit_final_mixture_strict_counterexample` | No completed statement check recorded. Lean translation recorded; Agent check by Codex PKG25 v10 semantic statement transcription 2026-07-24; 2026-07-24 | None recorded |
| Predictors must be measurable for P_i(X), calibration events, and the displayed expectations to be defined on an arbitrary measurable input space. | `source_assumption_predictor_measurability` | source condition; Agent check by Codex PKG25 independent semantic assumption audit 2026-07-24; 2026-07-24 | The source forms random reported probabilities, conditions on reported-probability events, and takes expectations under an arbitrary distribution. The unfolded condition requires each predictor P_i to be measurable, which is the standard model-definedness condition for those expressions; it neither changes the reliability conclusion nor supplies an advers... |
| For every measurable A in the reported-probability space, E[1_{P_i(X) in A,Y=1}]=E[P_i(X)1_{P_i(X) in A}] is the checked event-calibration interpretation of the source display. | `source_assumption_event_calibration` | source condition; Agent check by Codex PKG25 independent semantic assumption audit 2026-07-24; 2026-07-24 | The source requires calibrated predictors. Its point-fiber conditional display does not select a conditional value on a null fiber, so the reviewed model uses the explicitly documented, user-approved event identity for every measurable set of reported probabilities. This is a calibration reading of the source model, not an extra conclusion used to prove t... |
| The source's expected strategy accuracy requires measurability/integrability of the induced correctness indicator when C is an arbitrary deterministic function. | `source_assumption_strategy_expectation_well_formed` | source condition; Agent check by Codex PKG25 independent semantic assumption audit 2026-07-24; 2026-07-24 | The source defines an arbitrary deterministic strategy and then calls its expected binary correctness an accuracy. Predictor measurability alone does not make that induced indicator integrable on an arbitrary measurable space, so the unfolded condition is the analytic definedness condition for the displayed expectation. It is discharged by the finite witn... |
<!-- END GENERATED STATEMENT VALIDATOR LEDGER -->

## 21. Source-Coverage Audit Ledger

The source inventory contains 53 selected items: 42 have direct routes, eight
are covered by explicit theorem support, and three carry the approved model
conventions stated in Section 6. No advertised named conclusion is missing.

<!-- BEGIN GENERATED SOURCE COVERAGE LEDGER -->
### Current Canonical Evidence
- Coverage scope: full inventory shown because scope metadata needs repair (paper_statement_map.json must explicitly set source_coverage_mode before a source-coverage closeout).
- Source inventory: 53 source statements from `source.txt`.
- Coverage result: 3 conditional boundary, 42 covered, 8 support only.
- Coverage review: coverage ledger recorded; Agent check by Codex PKG25 source-first semantic coverage review 2026-07-24; 2026-07-24.
- Row-local statement checks: 0/64 linked row references have a completed canonical statement check; repeated links are counted per source row.

| Source statement | Linked Lean review rows | Coverage judgment | Row-local statement checks | Comments |
| --- | --- | --- | --- | --- |
| The opening display E[\|Yhat(X)-Y\|] is expected 0-1 loss, not accuracy; expected correctness is one minus this quantity. | None recorded | support only | No linked paper-facing row recorded | The support theorem states for every binary prediction and label-one probability that expected correctness equals one minus 0-1 loss. That is the precise correction of the opening display's mistaken accuracy label, so the printed formula is quarantined rather than counted as a proved source claim. |
| A predictor maps inputs to probabilities in [0,1]. | `source_formula_probability_predictor_range` | covered | `source_formula_probability_predictor_range`: no completed statement check | The reviewed statement quantifies a setting, agent, and input and proves both inequalities 0 <= P_i(x) and P_i(x) <= 1. It therefore covers the source definition's probability-valued predictor requirement. |
| The paper writes Pr[Y=1 \| P(X)=p]=p for each reported prediction value p. | `source_formula_probability_calibration`<br>`source_assumption_event_calibration` | conditional boundary | `source_formula_probability_calibration`: no completed statement check<br>`source_assumption_event_calibration`: no completed statement check | The source prints a point-conditioned equation. The checked model instead quantifies every measurable reported-probability event and equates its label-one mass with the prediction-weighted mass, which is the user-approved event-calibration reading and deliberately does not choose a conditional probability on a null fiber. |
| For every measurable A in the reported-probability space, E[1_{P_i(X) in A,Y=1}]=E[P_i(X)1_{P_i(X) in A}] is the checked event-calibration interpretation of the source display. | `source_formula_probability_calibration`<br>`source_assumption_event_calibration` | covered | `source_formula_probability_calibration`: no completed statement check<br>`source_assumption_event_calibration`: no completed statement check | Both linked rows expose the same all-measurable-set identity: indicator mass for label true equals the integral of the reported prediction over that event. This is exactly the recorded raw-joint-law event-calibration convention. |
| A collaboration setting is a probability distribution over inputs and binary labels together with n calibrated predictors. | `source_definition_probability_collaboration_setting` | covered | `source_definition_probability_collaboration_setting`: no completed statement check | The reviewed abbreviation expands the source setting to a raw joint law on inputs and binary labels together with its calibrated predictor family. It represents the source object without adding a selected pointwise conditional-label function. |
| Predictors must be measurable for P_i(X), calibration events, and the displayed expectations to be defined on an arbitrary measurable input space. | `source_assumption_predictor_measurability` | covered | `source_assumption_predictor_measurability`: no completed statement check | The explicit assumption requires every predictor in a joint-law collaboration setting to be measurable. That supplies the measurable reported-probability events needed by the calibration and expectation formulas. |
| Agent i's induced classifier rounds P_i(x), with round(1/2)=1. | `source_definition_rounding_convention`<br>`source_formula_probability_agent_classifier` | covered | `source_definition_rounding_convention`: no completed statement check<br>`source_formula_probability_agent_classifier`: no completed statement check | One row fixes the tie convention in roundProb and the other proves that the agent classifier is roundProb applied to its reported prediction. Together they cover both the rounding rule and the induced classifier formula. |
| Agent i's accuracy is E[max{P_i(X),1-P_i(X)}]. | `source_formula_probability_agent_accuracy` | covered | `source_formula_probability_agent_accuracy`: no completed statement check | The theorem proves that each agent's accuracy in the raw joint-law setting is the joint integral of max(P_i(x), 1-P_i(x)). This is the displayed individual-accuracy formula, derived from calibration rather than assumed pointwise. |
| A collaboration strategy maps n reported probabilities to a binary label. | `source_definition_collaboration_strategy` | covered | `source_definition_collaboration_strategy`: no completed statement check | The reviewed strategy type is a deterministic map from an n-coordinate real profile to a binary label. Its use on predictor profiles is separately constrained by the range theorem, matching the source strategy definition. |
| The induced classifier maps x to C(P_1(x),...,P_n(x)). | `source_formula_probability_strategy_classifier` | covered | `source_formula_probability_strategy_classifier`: no completed statement check | The reviewed equality evaluates the strategy classifier at x by passing the full function i \|-> P_i(x) to C. This is the source formula C(P_1(x), ..., P_n(x)). |
| a_C(S) is expected binary correctness of the collaboration classifier on setting S. | `source_formula_probability_strategy_accuracy`<br>`source_assumption_strategy_expectation_well_formed` | covered | `source_formula_probability_strategy_accuracy`: no completed statement check<br>`source_assumption_strategy_expectation_well_formed`: no completed statement check | The accuracy theorem identifies strategy accuracy with the joint integral of the binary correctness indicator, while the linked explicit condition records when that integral is well formed. This makes the source expectation definition precise on arbitrary measurable spaces. |
| The source's expected strategy accuracy requires measurability/integrability of the induced correctness indicator when C is an arbitrary deterministic function. | `source_assumption_strategy_expectation_well_formed` | covered | `source_assumption_strategy_expectation_well_formed`: no completed statement check | The explicit model condition names the requirement that the strategy correctness indicator is measurable and integrable before its expected accuracy is used. This is the recorded well-formedness convention for an arbitrary deterministic strategy. |
| C is reliable when, in every collaboration setting with defined strategy accuracy, its accuracy is at least one agent accuracy (equivalently at least the minimum when n is nonempty). | `source_formula_reliable_probability_iff` | covered | `source_formula_reliable_probability_iff`: no completed statement check | For a nonempty agent index, the reviewed equivalence expands reliability into: for every setting with defined strategy accuracy, some agent has accuracy no greater than the strategy. This is the source minimum-versus-agent formulation. |
| The source's min over i in [n] and its existential fixed agent require n to be nonzero. | `source_formula_reliable_probability_iff`<br>`source_proposition7_reliability_forces_fixed_deferral`<br>`source_proposition9_reliability_forces_fixed_tie_label` | covered | `source_formula_reliable_probability_iff`: no completed statement check<br>`source_proposition7_reliability_forces_fixed_deferral`: no completed statement check<br>`source_proposition9_reliability_forces_fixed_tie_label`: no completed statement check | Each linked source-facing result carries a Nonempty(Fin n) premise before choosing an agent or using the source minimum. The model convention is therefore visible at every result that needs a nonzero agent domain. |
| On every interior profile, C follows one fixed agent away from p_k=1/2 and returns one fixed label on the p_k=1/2 slice. | `source_formula_interior_prediction_profile_iff`<br>`source_formula_non_collaborative_iff` | covered | `source_formula_interior_prediction_profile_iff`: no completed statement check<br>`source_formula_non_collaborative_iff`: no completed statement check | The two rows identify interior profiles with coordinatewise values strictly between zero and one, then expand non-collaboration into one fixed agent followed away from one half and one fixed half-slice label. This is the full Definition 4 content. |
| Definition 4 leaves boundary profiles unconstrained; calibration makes a prediction of 0 or 1 certain on its reported-prediction event. | None recorded | support only | No linked paper-facing row recorded | This is post-Theorem-1 explanatory prose rather than a standalone result or theorem premise. Its two ingredients are separately exposed by the Definition 4 boundary interface and the event-calibration interface; the linked counterexample uses the boundary distinction only to refute the separately quarantined false iff. It is therefore retained as visible... |
| Every reliable collaboration strategy is non-collaborative. | `source_theorem1_no_free_lunch` | covered | `source_theorem1_no_free_lunch`: no completed statement check | The reviewed theorem takes a reliable strategy on a nonempty agent domain and concludes the source non-collaboration predicate. It is exactly the advertised forward no-free-lunch theorem under the visible raw-joint-law model conditions. |
| A prediction is correct at x when it equals the rounded conditional label probability at x. | `source_formula_correct_on_iff` | covered | `source_formula_correct_on_iff`: no completed statement check | The reviewed equivalence says that correctness of a binary prediction at an explicit finite-witness eta is exactly equality with the rounded eta. This covers the proof vocabulary without selecting a conditional-probability version on arbitrary null fibers. |
| A prediction is incorrect at x when it differs from the rounded conditional label probability at x. | `source_formula_incorrect_on_iff` | covered | `source_formula_incorrect_on_iff`: no completed statement check | The reviewed equivalence says that incorrectness at an explicit eta is inequality with its rounded binary label. This is the source proof vocabulary used in the finite witnesses. |
| Two agents or strategies agree at x when their binary predictions are equal. | `source_formula_agree_on_iff` | covered | `source_formula_agree_on_iff`: no completed statement check | The reviewed equivalence reduces agreement of two binary predictions to equality of their labels, which is exactly the source predicate definition. |
| Two agents or strategies disagree at x when their binary predictions differ. | `source_formula_disagree_on_iff` | covered | `source_formula_disagree_on_iff`: no completed statement check | The reviewed equivalence reduces disagreement of two binary predictions to inequality of their labels, which is exactly the source predicate definition. |
| If classifier i is correct whenever classifier j is correct, then i's accuracy is at least j's accuracy. | None recorded | support only | No linked paper-facing row recorded | The Lemma 8 witness proves the proof-relevant weak comparisons and one strict comparison by a finite case-table construction. It supports the observation's role in the source proof but is not a universal formalization of the prose implication. |
| The source claims that one positive-mass point where i is correct and j incorrect makes the accuracy comparison strict; this fails at a half tie under the stated rounding convention. | None recorded | support only | No linked paper-facing row recorded | The support theorem fixes eta=1/2, names one rounded label correct and the other incorrect, and proves their point accuracies equal. This is an exact counterexample to the source's unqualified strict-dominance claim, so the defective sentence is not directly covered. |
| For simplex weights over finitely many collaboration settings, a collaboration setting exists whose agent and strategy accuracies are the corresponding weighted sums. | `source_proposition6_linear_combination_settings` | covered | `source_proposition6_linear_combination_settings`: no completed statement check | Given nonnegative simplex weights, the reviewed theorem constructs one mixed setting and proves both agent-accuracy and well-formed strategy-accuracy weighted-sum equations. This is the Proposition 6 linear-combination statement. |
| The Proposition 6 prose says to sample m with probability lambda_ell after the displayed component equations use lambda_m. | None recorded | support only | No linked paper-facing row recorded | The support theorem uses the same quantified component index r in every weight, component setting, and weighted-sum equation. That checked construction refutes the prose sentence's inconsistent lambda_ell sampling index while preserving the intended mixture result. |
| The mixture scales component m's joint mass by lambda_m. | `source_formula_mixture_components` | covered | `source_formula_mixture_components`: no completed statement check | For every component r and measurable embedded joint event A, the reviewed theorem gives mixed mass ENNReal.ofReal(w r) times that component's mass. This is the full-joint-law version of the source mass scaling formula. |
| The mixture retains the component conditional label probability at (m,x). | `source_formula_mixture_components` | conditional boundary | `source_formula_mixture_components`: no completed statement check | The source wording selects a conditional label probability at each (m,x). The checked theorem instead preserves every embedded joint event and predictor value under mixing; this is the explicit raw-law replacement when a pointwise conditional version is not selected on null fibers. |
| Each mixed predictor at (m,x) equals its component predictor P_{i,m}(x). | `source_formula_mixture_components` | covered | `source_formula_mixture_components`: no completed statement check | The second conjunct of the reviewed mixture theorem states that the mixed predictor at tagged input (r,x) is exactly the r-th component predictor at x. This is the source predictor formula. |
| The source says a partition cell A induces P_i(x)=Pr[Y=1 \| X in A] for x in A. | `source_formula_probability_partition_induced_predictor` | conditional boundary | `source_formula_probability_partition_induced_predictor`: no completed statement check | The linked theorem establishes the printed positive-cell quotient under an explicit positive-mass premise. The separate null-cell, event-calibration, and setting rows implement the documented finite-partition reading, but do not separately claim the printed positive-cell formula. This remains the user-approved finite-partition boundary rather than a claim... |
| For a finite measurable partition, a positive-mass cell receives its true-label mass divided by cell mass; a null cell is explicitly assigned 0, and the resulting predictor is event-calibrated. | `source_formula_probability_partition_induced_predictor`<br>`source_convention_probability_partition_zero_mass_prediction`<br>`source_probability_partition_predictor_calibrated_events`<br>`source_probability_partition_collaboration_setting` | covered | `source_formula_probability_partition_induced_predictor`: no completed statement check<br>`source_convention_probability_partition_zero_mass_prediction`: no completed statement check<br>`source_probability_partition_predictor_calibrated_events`: no completed statement check<br>`source_probability_partition_collaboration_setting`: no completed statement check | The four linked rows prove the positive-cell quotient, the explicit zero value on a null cell, all measurable-event calibration equations, and the resulting collaboration-setting package. Together they state exactly the finite measurable partition repair used by the witness constructions. |
| The proof section restates reliability iff non-collaboration, but Definition 4 leaves boundary behavior unconstrained, so only the forward implication is valid. | None recorded | support only | No linked paper-facing row recorded | The support theorem proves one boundary-flipping strategy satisfies the interior non-collaboration predicate while failing raw-joint-law reliability. This directly counters the printed converse direction, leaving only the source theorem's forward implication. |
| Reliability forces one fixed agent k followed at every interior profile with p_k not equal to 1/2. | `source_proposition7_reliability_forces_fixed_deferral` | covered | `source_proposition7_reliability_forces_fixed_deferral`: no completed statement check | The reviewed proposition takes a reliable strategy on a nonempty agent domain and concludes that some fixed k satisfies the off-half deferral predicate. This is the Proposition 7 conclusion. |
| A uniform mixture of the n Lemma 8 settings makes the strategy strictly less accurate than every agent. | `source_proposition7_uniform_mixture_strict_counterexample` | covered | `source_proposition7_uniform_mixture_strict_counterexample`: no completed statement check | Under failure of every fixed deferral choice, the reviewed theorem constructs one setting whose strategy accuracy is strictly below every agent accuracy. This is the uniform Lemma 8 mixture contradiction used in Proposition 7. |
| A bad interior tuple away from agent k's half tie yields a collaboration setting where k strictly beats C and every other agent weakly beats C. | `source_lemma8_bad_tuple_counterexample_setting` | covered | `source_lemma8_bad_tuple_counterexample_setting`: no completed statement check | For an interior profile, a non-half coordinate k, and disagreement between C and round(p_k), the reviewed lemma constructs a setting where C is strictly below k and weakly below every agent. This is the stated Lemma 8 witness result. |
| Lemma 8 uses input points {0,...,n} and agent i's partition cell {0,i} with all remaining points singleton. | `source_formula_lemma8_labels_and_predictions`<br>`source_lemma8_partition_realization` | covered | `source_formula_lemma8_labels_and_predictions`: no completed statement check<br>`source_lemma8_partition_realization`: no completed statement check | The first row gives the center and agent-point prediction table on Part1Point, while the partition-realization theorem proves that the source cell map yields those predictions. Together they cover the n+1-point space and each {0,i} versus singleton partition. |
| At point 0 the conditional label probability is 1-C(p), while at each agent point it is C(p). | `source_formula_lemma8_labels_and_predictions` | covered | `source_formula_lemma8_labels_and_predictions`: no completed statement check | The reviewed table states that the center label probability is the complement of C(p) and every agent point has label probability C(p). This is the source label assignment for Lemma 8. |
| When C(p)=0, point 0 has normalized unit mass and point i has normalized odds (1-p_i)/p_i. | `source_formula_lemma8_masses` | covered | `source_formula_lemma8_masses`: no completed statement check | The mass theorem gives the false-output odds (1-p_i)/p_i, the unit center numerator, the per-agent normalized numerator, and their common denominator. These are the source C(p)=0 masses. |
| When C(p)=1, point 0 has normalized unit mass and point i has normalized odds p_i/(1-p_i). | `source_formula_lemma8_masses` | covered | `source_formula_lemma8_masses`: no completed statement check | The same mass theorem gives the true-output odds p_i/(1-p_i), the unit center numerator, the per-agent normalized numerator, and their common denominator. These are the source C(p)=1 masses. |
| For each i, the {0,i} cell has conditional label probability p_i, making the constructed predictor calibrated. | `source_lemma8_partition_realization`<br>`source_lemma8_witness_calibrated` | covered | `source_lemma8_partition_realization`: no completed statement check<br>`source_lemma8_witness_calibrated`: no completed statement check | The partition-realization theorem identifies every source cell predictor with the displayed Part1 prediction, and the calibration theorem gives the label-mass equals prediction times event-mass equation for every reported value. This covers the {0,i} cell calibration claim. |
| At point 0 the vector of constructed predictions is exactly the bad profile p. | `source_formula_lemma8_labels_and_predictions` | covered | `source_formula_lemma8_labels_and_predictions`: no completed statement check | At the center point none, the reviewed prediction table states part1Pred b p i none = p i for every i. Thus the entire center profile is exactly the bad tuple p. |
| The normalized odds make the center mass at least each paired point mass, strictly for the bad non-half coordinate, yielding the weak and strict accuracy inequalities. | `source_lemma8_bad_tuple_counterexample_setting` | covered | `source_lemma8_bad_tuple_counterexample_setting`: no completed statement check | The constructed setting conclusion gives C strictly below agent k and weakly below every agent under exactly the bad-tuple hypotheses. It is the checked accuracy consequence of the normalized odds argument, not merely a restatement of the construction data. |
| Given fixed off-half deferral to k, reliability forces one fixed output alpha on every interior p_k=1/2 profile. | `source_proposition9_reliability_forces_fixed_tie_label` | covered | `source_proposition9_reliability_forces_fixed_tie_label`: no completed statement check | Given reliability and a fixed off-half deferral agent k, the reviewed proposition produces one alpha satisfying the constant-half-slice predicate. This is the Proposition 9 fixed tie-label conclusion. |
| S1 has masses 1/3 and 2/3, conditional label probabilities epsilon and 1-epsilon, and the displayed pooled agent-k prediction. | `source_formula_proposition9_s1_family`<br>`source_proposition9_s1_partition_realization` | covered | `source_formula_proposition9_s1_family`: no completed statement check<br>`source_proposition9_s1_partition_realization`: no completed statement check | The S1 family theorem gives masses 1/3 and 2/3, label probabilities epsilon and 1-epsilon, and the pooled k prediction 2/3-epsilon/3. The realization theorem connects that finite setting to the exact source partition cells. |
| In S1, agent k uses the pooled prediction 2/3-epsilon/3 at both points, every other agent uses the corresponding conditional label probability, and the resulting finite prediction cells are calibrated. | `source_formula_proposition9_s1_family`<br>`source_proposition9_s1_partition_realization` | covered | `source_formula_proposition9_s1_family`: no completed statement check<br>`source_proposition9_s1_partition_realization`: no completed statement check | The S1 family theorem gives the k and non-k prediction table and a positive-cell calibration equation for every agent and reported value. The partition-realization theorem then proves the finite source cell map produces those predictors, covering the source finite-witness calibration formula. |
| The S1 construction requires 0 < epsilon < 1/2 because it uses epsilon and 1-epsilon as probabilities and its profiles as elements of (0,1)^n, although the source prints only epsilon < 1/2. | None recorded | support only | No linked paper-facing row recorded | The support theorem makes both 0 < epsilon and epsilon < 1/2 explicit and derives probability ranges plus interiority of every S1 prediction profile. It refutes treating the printed upper bound alone as sufficient for the claimed construction. |
| In S1, agent k and C have accuracy 2/3-epsilon/3, while all other agents have accuracy 1-epsilon and are strictly more accurate for 0 < epsilon < 1/2. | `source_proposition9_s1_parameterized_accuracy_gap` | covered | `source_proposition9_s1_parameterized_accuracy_gap`: no completed statement check | Under 0 < epsilon < 1/2 and off-half deferral, the reviewed theorem gives C and k accuracy 2/3-epsilon/3, every other agent accuracy 1-epsilon, and the strict inequality. This is the source S1 accuracy calculation. |
| Failure of a constant half-slice label yields interior profiles p and q with p_k=q_k=1/2 and C(p)=1, C(q)=0. | `source_proposition9_s2_strict_gap` | covered | `source_proposition9_s2_strict_gap`: no completed statement check | The strict-gap theorem assumes interior p and q, p_k=q_k=1/2, and opposite C outputs, then uses their two center profiles in the S2 witness. These are exactly the witness-profile conditions extracted from failure of a fixed half-slice label. |
| S2 uses two copies of the n+1-point Lemma 8 input space. | `source_formula_proposition9_s2_construction`<br>`source_proposition9_s2_partition_realization` | covered | `source_formula_proposition9_s2_construction`: no completed statement check<br>`source_proposition9_s2_partition_realization`: no completed statement check | The construction has points tagged by a Boolean copy and a Part1Point, while the realization theorem ranges over the corresponding Part2S2Point cells. Together they represent the two copies of the Lemma 8 input space and their source partitions. |
| The printed S2 masses contain a free-index q-odds term in their common denominator and therefore do not literally specify one normalized distribution. | None recorded | support only | No linked paper-facing row recorded | The support theorem fixes one denominator D as 2 plus the finite sum of both p-odds and q-odds terms. This exact repaired expression refutes the printed free-index denominator, which cannot define one normalized S2 distribution. |
| The repaired S2 law uses D=2+sum_j(p_j/(1-p_j)+(1-q_j)/q_j), then the displayed p-copy and q-copy normalized masses and labels. | `source_formula_proposition9_s2_repaired_normalizer`<br>`source_proposition9_s2_repaired_mass_normalized`<br>`source_formula_proposition9_s2_construction` | covered | `source_formula_proposition9_s2_repaired_normalizer`: no completed statement check<br>`source_proposition9_s2_repaired_mass_normalized`: no completed statement check<br>`source_formula_proposition9_s2_construction`: no completed statement check | The linked rows state the repaired single denominator, prove the finite S2 mass function sums to one under interiority, and give the two copy weights, masses, labels, and predictions. This is explicitly the checked repair rather than a claim that the printed formula was valid. |
| The paired cells in copy 0 have conditional label probability p_i and those in copy 1 have conditional label probability q_i. | `source_proposition9_s2_partition_realization`<br>`source_proposition9_s2_calibrated` | covered | `source_proposition9_s2_partition_realization`: no completed statement check<br>`source_proposition9_s2_calibrated`: no completed statement check | The realization theorem equates each finite source-cell predictor to the displayed S2 predictor, and the calibration theorem gives the event label-mass equation for every agent and reported value. This covers the p-copy and q-copy cell calibration equations of the repaired law. |
| The two center predictor profiles equal p and q; C is wrong at both centers while k is correct at one, so C is strictly less accurate than k. | `source_proposition9_s2_strict_gap` | covered | `source_proposition9_s2_strict_gap`: no completed statement check | The reviewed conclusion identifies the two S2 center prediction functions with p and q and proves strategy accuracy strictly below agent k. It is the source profile-and-gap calculation under the displayed half-slice hypotheses. |
| Mixing S1 with weight lambda and S2 with weight 1-lambda preserves the componentwise accuracy equations; a lambda close enough to one makes every agent strictly beat C. | `source_formula_proposition9_explicit_final_mixture`<br>`source_proposition9_explicit_final_mixture_strict_counterexample` | covered | `source_formula_proposition9_explicit_final_mixture`: no completed statement check<br>`source_proposition9_explicit_final_mixture_strict_counterexample`: no completed statement check | One theorem supplies the exact 7/8 and 1/8 componentwise accuracy equations, and the other constructs a mixed setting where C is strictly below every agent from the S2 half-slice hypotheses. These are the checked explicit-weight form of the source final-mixture argument. |
<!-- END GENERATED SOURCE COVERAGE LEDGER -->
