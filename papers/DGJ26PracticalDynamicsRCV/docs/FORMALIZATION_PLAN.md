# Formalization Plan: Simpler Than You Think: The Practical Dynamics of Ranked Choice Voting

This is a working scratchpad for outside-Lean proof thinking. Keep it short and
useful; it is not the final validation report.

- Namespace: `DGJ26PracticalDynamicsRCV`

## Initial Outside-Lean Paper Audit

- Source version / local files inspected: arXiv:2602.14329 and local
  `source.pdf` / `source.txt`; official DOI page recorded in the README.
- Source/version mismatch notes: source is the arXiv PDF; the official journal
  page may differ and must be checked before final validation.
- Complete named-result ledger status: first-pass source-text inventory
  completed.
- Formula sanity check:
  - Signs, constants, normalizations, quantifiers, domains: not fully checked.
    The critical formulas are the robust-allocation inequalities in Proposition
    1, the exhausted-ballot threshold `g_c <= E_{r_c-1}`, and the strengthened
    removal conditions in Theorems 2.1 and 2.2.
  - Density vs mass / likelihood-kernel representation issues: not applicable;
    this paper is finite STV/RCV plus empirical election audits.
  - Dependency map between named source results: Proposition 1 and Proposition
    2 depend on the prior SmartAllocation / candidate-removal framework;
    Theorem 2.1 strengthens Algorithm 2; Theorem 2.2 extends containment to
    early-winner multi-winner settings.
  - Formula-bearing displayed claims that need derivation, not source-row
    assumptions: inequalities (1)--(3), Algorithm 3/4 conditions, and
    exhausted-ballot viability thresholds.
- Named result sanity check:
  - Results that look correct as stated: no contradiction found in the initial
    scan; most theorem statements are natural application wrappers over the
    first paper's algorithms.
  - Suspected bugs, missing assumptions, or ambiguous wording: empirical
    thresholds and runtime reports should be data/code boundaries; optimality
    depends on the first paper's SmartAllocation/irrelevant-candidate removal
    semantics.
- Shared-library reuse checkpoint:
  - Mathlib declarations/modules inspected: finite lists/finsets through the
    new `Voting` skeleton.
  - Cslib declarations/modules inspected: none yet.
  - Optlib declarations/modules inspected: none present in this checkout.
  - Existing `EconCSLib` declarations/modules inspected:
    `EconCSLib.SocialChoice.Voting` and the `DGJ24OptimalStrategiesRCV`
    scaffold.
  - API chosen and near-misses: reuse the first paper's fixed-structure and
    candidate-removal APIs once built; do not duplicate SmartAllocation
    semantics locally.
- Proof strategy consequences:
  - Source proof route to follow: formalize this paper only after the first
    paper exposes reusable strategy/candidate-removal certificate APIs.
  - Cleaner Lean route or reusable library route: implement robustness as
    transformations of strategy certificates over the shared ballot/trace API.
  - Major issues already reported to the user: roadmap author metadata was
    stale and has been corrected.

## Source Inventory

- Definitions / formatted paper objects:
  - Robust allocation, exhausted-ballot completion, irrelevant-candidate
    removal, strict support, extended removal condition, and multi-winner
    containment.
- Named lemmas / propositions / theorems / corollaries:
  - Proposition 1, Proposition 2, Theorem 2.1, Theorem 2.2, Definition B.1,
    Lemma B.2, Algorithm 1, Algorithm 2, Algorithm 3, Algorithm 4, Algorithm A,
    and Algorithm B.
- Theorem-like displayed claims that are used later:
  - Robust transfer inequality (1), exhausted-ballot viability condition,
    extended-removal inequalities, and containment conditions for early winners.

## Initial Proof Strategy

- Main theorem chain: first-paper SmartAllocation and candidate-removal
  certificates -> Proposition 1 robustness -> Proposition 2 exhausted-ballot
  completion -> Theorems 2.1/2.2 strengthened removal and containment.
- Likely reusable `EconCSLib` seams: prefix/suffix ballot robustness,
  exhausted-ballot completion equivalence, and candidate-removal certificate
  transformations.
- Paper steps that look underspecified or analytically hard: polynomial-time
  runtime statements, empirical traceability thresholds, and runtime evidence.
- Formal target map:
  - Rows to fully prove now: none beyond compileable source-vocabulary anchors
    until first-paper fixed-structure APIs exist.
  - Empirical/descriptive rows out of formal theorem scope: 110-election audit
    findings, NYC/Portland examples, threshold gains, and runtime tables.
  - Explicit assumption/certificate boundaries, if any: imported first-paper
    algorithm correctness, robust transfer certificate, and data/code boundary.
- Planned fallback route if the source proof is too informal: expose
  transformation certificates over first-paper strategy outputs and mark
  theorem rows partial until those certificates are constructed.

## Reusable-Library TODO

- Library APIs to use directly:
  `EconCSLib.SocialChoice.Voting.Ballot.nextActive`,
  prefix/suffix-extension lemmas, exhausted-prefix completion lemmas, and the
  DGJ24 SmartAllocation / candidate-removal certificate APIs once their
  constructors are source-shaped.
- Small reusable lemmas added now:
  suffixing preserves the first active candidate, inactive prefixes preserve
  `nextActive`, and appending a strategy to an exhausted ballot is equivalent
  to the strategy ballot at the current active set.  The original Algorithm 2
  strict-support group-removal condition now reuses the shared
  `EconCSLib.SocialChoice.Voting.STV` group-removal predicate instead of a
  DGJ26-local duplicate.
- Larger reusable components to defer:
  Algorithm A robust-allocation certificate, strengthened Algorithm 2 removal
  source-shaped certificate for Theorem 2.1, and multi-winner containment
  source-shaped certificate for Theorem 2.2.
- Library-audit risks:
  do not duplicate the DGJ24 SmartAllocation or candidate-removal semantics
  locally; DGJ26 should be a wrapper/application layer once those APIs exist.

## Execution Checklist

- [ ] Download/cache source PDFs and text extracts, with redistribution notes.
- [x] Complete named-result and formula-bearing displayed-claim inventory for
      the current Proposition 1/2 and Theorem 2.1/2.2 source map.
- [x] Fill the formal target map and declare the current boundary/certificate
      rows.
- [x] Build or select reusable library APIs before adding paper-local wrappers.
- [x] Replace paper scaffold with source-facing Lean definitions and rows for
      the ballot-level Proposition 1/2 subclaims.
- [ ] Prove all rows marked in-scope, or downgrade them with an explicit
      boundary note.
- [x] Update README and status from the same row list.
- [x] Run build plus statement/coverage/assumption prechecks for the current
      partial review surface.
- [ ] Record any unresolved source bug, assumption, or library debt.

## Active Scratchpad

- Current Lean endpoint:
  `paper_proposition1_suffix_robust_first_active`,
  `paper_proposition1_prefix_robust_first_active`,
  `paper_proposition1_suffix_robust_active_support_count`,
  `paper_proposition1_prefix_robust_active_support_count`,
  `paper_proposition1_robust_extension_optimal_and_runtime`,
  `paper_proposition1_from_robust_extension_certificate`,
  `paper_robust_smart_allocation_slack_reduction_certificate`,
  `paper_proposition1_from_smart_allocation_slack_reduction_certificate`,
  `paper_proposition2_exhausted_completion_equivalent`, and
  `paper_proposition2_exhausted_completion_activates_candidate`, plus the
  profile-level completion row
  `paper_proposition2_exhausted_completion_active_support_count`, plus the
  Proposition 2 viable-candidate rows `paper_exhausted_completion_viable`,
  `paper_exhausted_completion_viable_candidates`, and
  `paper_proposition2_viable_candidates_characterization`, plus the
  robust-extension certificate row `paper_robust_extension_certificate`, the
  Definition B.1 strict-support row `paper_strict_support_count`, Algorithm
  2/3 rows `paper_original_candidate_removal_condition`,
  `paper_extended_candidate_removal_condition`, and
  `paper_one_survival_round_safety`, and
  `paper_algorithm3_extended_condition_of_original_condition`, plus the
  Theorem 2.2 formula rows `paper_weighted_surplus_transfer_bound`,
  `paper_lower_candidate_transfer_bound`,
  `paper_updated_upper_candidate_support_bound`, and
  `paper_multiwinner_updated_strict_support_condition`, plus the
  Algorithm 3 one-survival step certificate
  `paper_one_survival_step_certificate` and proof
  `paper_algorithm3_one_survival_step_removes_lower`, plus the
  Algorithm 3 candidate-level original-condition failure trigger
  `paper_extended_removal_original_failure` and strongest step-trace
  Theorem 2.1 route
  `paper_theorem2_1_from_step_trace_certificate`, plus the
  Theorem 2.1/2.2 source-shaped certificate projections
  `paper_theorem2_1_strengthened_removal_sound_and_quartic_runtime` and
  `paper_theorem2_2_multiwinner_containment_sound_and_polynomial_runtime`,
  the Algorithm 3 condition-certificate projection
  `paper_theorem2_1_from_extended_removal_condition`,
  the Algorithm 3 trace/one-survival certificate projection
  `paper_theorem2_1_from_trace_or_one_survival_certificate`,
  and the Algorithm 4 condition-certificate projection
  `paper_theorem2_2_from_updated_strict_support_condition`,
  plus the Theorem 2.2 Eq. (2)/(3) arithmetic checks
  `paper_weighted_surplus_transfer_bound_le_next_choice_votes`,
  `paper_lower_candidate_transfer_bound_le_next_choice_plus_unweighted`, and
  `paper_base_support_le_updated_upper_candidate_support_bound`,
  build under `lake build EconCSLib.SocialChoice.Voting.STV` followed by
  `lake env lean papers/DGJ26PracticalDynamicsRCV/PaperInterface.lean`.
- Exact current mathematical gap:
  Proposition 1 now has a DGJ24 SmartAllocation slack-reduction route:
  a certified robust output transform over the prior paper's checked
  SmartAllocation slack certificate yields optimality and the linear runtime
  bound, and the suffix/prefix robustness algebra is closed at both the
  first-active ballot level and the profile-level active-support count level.
  The remaining Proposition 1 bridge is the concrete Algorithm A
  robust-output constructors that instantiate that source-shaped route for
  suffix/prefix/length-restricted transforms. Proposition 2 still needs the
  concrete Algorithm A required-vote and exhausted-ballot-availability inputs
  that instantiate the viable-candidate set formula; the exhausted-prefix
  active-support preservation algebra is now closed. Theorem 2.1's original
  Algorithm 2 branch is
  now discharged from certified minimum-tally STV traces via the shared
  strict-support group-removal library; the one-survival branch now has a
  source-shaped post-transfer step certificate proving the lower candidate is
  removed after the worst upper candidate, and the strongest current
  step-trace certificate wires those one-survival step certificates into the
  Theorem 2.1 projection. The remaining Theorem 2.1 bridge is connecting the
  original-branch and one-survival removal facts to the concrete reduced-instance
  preservation specification. Theorem 2.2 now has the concrete retained/removed
  output theorem, the exact `uniqueBallotCount * candidateCount ^ 2`
  verification-bound route, and the quadratic component-bound implementation
  route. The remaining Theorem 2.2 bridge is extracting the source pairwise
  inequalities from the full multi-winner election-run semantics; the weighted
  surplus-transfer, total lower-candidate transfer, updated upper-candidate
  support, updated strict-support formulas, and basic Eq. (2)/(3) arithmetic
  bounds are already packaged into the condition certificate layer.
- Next bridge lemmas to try:
  wait for the DGJ24 SmartAllocation and irrelevant-candidate-removal
  constructors before duplicating algorithm semantics. The next useful DGJ26
  constructor is a robust-allocation certificate that combines suffix/prefix/
  length ballot invariants with the DGJ24 slack certificate and feeds the new
  shared optimization output-transform lift.
- Informal proof sketch / recurrence / construction:
  Proposition 1 should transform a fixed-structure allocation certificate into
  a robust allocation certificate by showing suffix choices do not alter first
  active candidates once the strategy ballot has reached one, irrelevant or
  exhausted prefixes do not alter the strategy ballot's active candidate, and
  length restrictions are enforced by the certificate's ballot-generation
  component. Proposition 2 then treats exhausted prefixes as already inactive
  prefixes to Algorithm A's strategy ballots.

## Deviations And Assumptions

- Source imprecision or proof deviation to report later:
- Genuine paper assumptions to declare in `Assumptions.lean`:
  none for the current ballot-level rows.
- Temporary certificate fields to discharge:
  Algorithm A robust-allocation feasibility/objective/runtime preservation,
  Algorithm A exhausted-ballot viable-candidate characterization, strengthened
  Algorithm 2 one-survival removal constructor for the source-shaped
  certificate, and Theorem 2.2 multi-winner containment constructor for the
  source-shaped certificate.
- Validation/audit checks that must inspect these assumptions:
  statement and coverage sidecars currently mark Proposition 1/2 theorem rows
  as conditional ballot-level boundaries and Theorem 2.1/2.2 as conditional
  source-shaped certificate boundaries; assumption provenance remains empty.
