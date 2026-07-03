# Final Validation Report: A No Free Lunch Theorem for Human-AI Collaboration

Updated: 2026-07-03

## 1. Human Verdict
Formalized. The main theorem proof is checked for finite calibrated settings
and explicit mixtures. No major paper-correctness issue is reported; one minor
display uses loss notation where the surrounding text and proof use accuracy.
No human dashboard sign-off has been recorded.

## 2. Closeout Status
- Completion status: formalized.
- One-sentence recap: The no-free-lunch theorem surface is formalized with explicit finite mixture and loss/accuracy conventions.
- Lean footprint: 2,030 paper-local Lean LOC; `PaperInterface.lean` is 163 lines; 15 human-review declarations are exposed.
- Audit summary: source coverage has 15 covered; statement LLM-as-judge has 15 matches; Lean-to-TeX has 15 row translations; assumption provenance sidecar is not tracked; source-record classification sidecar is not tracked; source-record audit reports 6 review rows, 0 boundary inputs, 0 recursion failures; review-surface audit passes over 15 review rows; holistic source-first audit PASS; DAG/source-json audit PASS in `docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`.

## 3. Source and Scope
- Paper: *A No Free Lunch Theorem for Human-AI Collaboration*
- Authors: Kenny Peng, Nikhil Garg, Jon Kleinberg
- Source version: Proceedings of the AAAI Conference on Artificial Intelligence, 39(13), 14369-14376 (AAAI 2025)
- Lean folder: `papers/PKG25NoFreeLunch`
- Human-facing theorem file: `papers/PKG25NoFreeLunch/PaperInterface.lean`
- DAG artifacts: `papers/PKG25NoFreeLunch/docs/DependencyDAG.tex`, `papers/PKG25NoFreeLunch/docs/DependencyDAG.pdf`

## 4. Researcher Summary of Checked Results
- The finite collaboration setting, calibration condition, deterministic strategies, source reliability, and non-collaboration definitions are formalized.
- The main no-free-lunch theorem is proved through explicit finite counterexample settings and mixtures.
- The proof replaces a qualitative closeness phrase by an explicit mixture weight where needed.

## 5. Remaining Boundaries and Gaps
None.

## 6. Additional Assumptions Beyond Paper
None.

## 7. Proof-Strategy Deviations
- Proposition 2 source route: the paper says to choose `lambda`
  sufficiently close to 1. Lean route: the proof uses the explicit `7/8` and
  `1/8` mixture weights. This removes qualitative closeness wording while
  proving the same finite counterexample endpoint.

## 8. Proof Tricks Worth Reusing
- Use a finite setting structure with explicit masses, label probabilities, and calibrated predictions.
- Prove zero-mass calibration cells by finite nonnegative sums, so calibration can be used unconditionally.
- Model mixtures as sigma/disjoint-union finite settings and prove strategy/agent accuracy linearity once.
- For no-free-lunch counterexamples, prove pointwise dominance plus one strict positive-mass point, then lift with `Finset.sum_lt_sum`.

## 9. Mathematical Typos or Other Fixes Suggested in the Source Paper
The early display `E |Yhat(X) - Y|` is treated as loss notation. The
formalization follows the surrounding text and proof, which use accuracy as
expected correctness.

## 10. Paper Issues or Caveats
One minor display uses loss notation where the surrounding text and proof use accuracy. No major paper-correctness issue is reported.

## 11. Detailed Formalization Evidence
- The finite collaboration-setting model, calibration condition, deterministic strategies, source reliability, and non-collaboration definitions are formalized.
- The source linear-combination proposition is formalized as a disjoint-union mixture of finite calibrated settings.
- Proposition 1 is proved from the explicit counterexample setting for each failed deferral coordinate, then mixed across agents.
- Proposition 2 is proved from the source's two auxiliary finite settings. The "lambda close to 1" step is replaced by an explicit `7/8` and `1/8` mixture.
- The main theorem `theorem_main_no_free_lunch` proves that every reliable deterministic collaboration strategy is non-collaborative.

The nonempty finite agent set and deterministic strategy class are source model
conditions. The exposed theorem uses source reliability over all
collaboration-setting accuracy surfaces, and the proof instantiates that
reliability premise on the finite calibrated witness settings constructed in
the source proof.

## 12. Paper Assumption Provenance
No paper-facing assumption rows are tracked for this paper; the generated
validator summary above is the current assumption-provenance status. Source
model conditions are exposed directly in the theorem statements and detailed
evidence rather than as separate assumptions.

## 13. Displayed Formula Provenance
Displayed and source-defining formulas are tracked through the paper-facing rows in `PaperInterface.lean` and the current statement-match sidecars. This report pass found no standalone formula-provenance issue beyond any source notes already listed above.

## 14. Library Lift Pass
- Candidate reusable components: finite calibrated setting mixtures, finite event-mass scaling lemmas, and finite accuracy range lemmas.
- These currently live paper-locally because the API may need another paper before stabilizing.

## 15. DAG Audit
- Rendered artifact: `DependencyDAG.pdf` regenerated from `DependencyDAG.tex`
- Topology: source proof dependencies are reflected in `DependencyDAG.tex`
- Layout: visually inspected after regeneration; nodes and labels are readable without text collisions

## 16. Validation Checks

<!-- BEGIN GENERATED LLM-AS-JUDGE RESULTS -->
### LLM-as-Judge Results
- Source coverage (`audit/paper_coverage_llm.json`): 15 covered.
- Statement match (`audit/statement_match_llm.json`): 15 matches.
- Lean-to-TeX translations (`audit/lean_to_tex_llm.json`): 15 row translations generated from Lean statements.
- Assumption provenance: no assumption-match sidecar tracked for this paper.
- Source-record classification: no source-record classification sidecar tracked for this paper.
- Source-record structural audit (`audit/source_record_audit.json`): 6 review rows, 0 boundary inputs, 0 recursion failures.
- Review-surface audit (`audit/review_surface_llm.json`): passes over 15 review rows.
- Holistic source-first audit (`docs/AGENT_SOURCE_AUDIT.md`): PASS.
- DAG/source/source-json audit (`docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`): PASS.
<!-- END GENERATED LLM-AS-JUDGE RESULTS -->

- `lake build PKG25NoFreeLunch` passes.
- `latexmk -pdf -interaction=nonstopmode -halt-on-error DependencyDAG.tex` passes.
- Lean axiom checks for `reliableFinite_exists_defers_away`, `reliableFinite_constant_on_half`, `main_no_free_lunch_finite`, `reliableFinite_of_reliable`, `main_no_free_lunch`, and `theorem_main_no_free_lunch` report only the ordinary Lean/Classical base axioms `propext`, `Classical.choice`, and `Quot.sound`.
- `python3 scripts/review_dashboard.py --paper PKG25NoFreeLunch --statement-check` reports six current Lean-to-TeX drafts, six statement-judge rows, and no missing/stale/flagged items.

## 17. Paper Definitions Checked
- `definition_rounding_convention`: source rounding convention `round(1/2) = 1`.
- `definition_collaboration_strategy`: deterministic collaboration strategy from prediction profiles to labels.
- `definition_interior_prediction_profile`: source domain `(0,1)^n`.
- `definition_non_collaborative`: fixed agent off ties and fixed tie label on the half slice.
- `definition_reliable`: source reliability over all collaboration-setting accuracy surfaces.

## 18. Named Theorem Statements Checked
### Theorem 1
**Paper statement.** Every reliable collaboration strategy is non-collaborative.

**Lean interface statement.**
- `theorem_main_no_free_lunch`: for a nonempty finite agent set, `Reliable C -> NonCollaborative C`.

**Status.** formalized.

## 19. Paper-Facing Statement Validator Ledger
Current source: `audit/statement_match_llm.json`, refreshed 2026-06-29.

| Validator surface | Result |
| --- | --- |
| Statement match | 15 matches. |
| Lean-to-TeX drafts | 15 row translations generated from Lean statements. |
| Assumption provenance | no assumption-match sidecar tracked. |
| Source coverage | 15 covered. |

The full row-level validator ledger is tracked in the JSON sidecars. Human
dashboard reviews and model/agent statement checks are separate provenance lanes;
this report does not change the human-only `human_review.reviewed_rows` counter.
