# Final Validation Report: Combatting Gerrymandering with Ranked Choice Voting

Updated: 2026-07-03

## 1. Human Verdict
The in-scope theorem ledger is formalized. Lemma C.1, the PAV rounding path,
solid-coalition STV isolation, Droop-quota arithmetic, and Proposition 1 are
closed in Lean through the 19 paper-facing rows in `PaperInterface.lean`.

No human dashboard sign-off has been recorded.

## 2. Closeout Status
- Completion status: formalized.
- One-sentence recap: The STV solid-coalition guarantee used by the gerrymandering analysis is formalized on the theoretical result surface.
- Lean footprint: 9,398 paper-local Lean LOC; `PaperInterface.lean` is 403 lines; 19 human-review declarations are exposed.
- Audit summary: source coverage has 19 covered; statement LLM-as-judge has 19 matches; Lean-to-TeX has 19 row translations; assumption provenance sidecar has no rows; source-record classification has 2 proved_from_primitives, 2 validated_source_assumption; source-record audit reports 19 review rows, 4 boundary inputs, 0 recursion failures; review-surface audit passes over 19 review rows; holistic source-first audit PASS; DAG/source-json audit PASS in `docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`.

## 3. Source and Scope
The formalized source version is the arXiv paper with Operations Research 2026
metadata recorded in `README.md`. The theorem ledger covers the theoretical
Lemma C.1 and Proposition 1 path.

Redistricting optimization, map generation, simulations, and empirical claims
remain data/code scope outside this theorem ledger.

## 4. Researcher Summary of Checked Results
- PAV/Thiele committee-score vocabulary and two-party PAV seat-score wrappers.
- Lemma C.1 PAV interval and interval-to-rounded-seat-share consequences.
- Solid-coalition ballot party-isolation bridge for STV traces.
- Droop-quota and proportionality arithmetic used by Proposition 1.
- Proposition 1 from the generated filled-seat fractional STV source run and
  the PAV min-argmax theorem to rounded STV/PAV seat shares.

## 5. Remaining Boundaries and Gaps
None for the theorem ledger. The remaining non-Lean scope is empirical/data/code
work: district generation, simulations, and redistricting optimization.

## 6. Additional Assumptions Beyond Paper
None.

## 7. Proof-Strategy Deviations
None. The final STV statement reads the party result through `partyFilledSeatCount` on the generated filled-seat run; that is checked accounting for the source result, not a substantive departure from the paper proof.

## 8. Proof Tricks Worth Reusing
- Model terminal fill candidates separately from quota-election rounds.
- Use `partyFilledSeatCount` to count elected candidates plus terminal fill
  candidates in a source-level filled-seat STV run.
- Keep `PaperInterface.lean` to the review surface; leave historical proof
  route aliases in implementation files.

## 9. Mathematical Typos or Other Fixes Suggested in the Source Paper
None found.

## 10. Paper Issues or Caveats
No source-quality caveat is recorded for the formalized theoretical theorem
ledger.

## 11. Detailed Formalization Evidence
- `PaperInterface.lean` exposes 19 source-facing definitions and theorem rows.
- `MainTheorems.lean` contains the implementation route from PAV/Thiele
  arithmetic, solid-coalition STV isolation, filled-seat STV accounting, and
  Droop-quota bounds to Proposition 1.
- `EconCSLib.SocialChoice.Voting.STV.SolidCoalition` now contains reusable
  filled-seat total-count and two-party decomposition lemmas.
- The final Proposition 1 theorem exposes source model hypotheses directly,
  including `choice.Total` and quota-respecting choice for the Droop quota.

## 12. Paper Assumption Provenance
No paper-local assumption rows are tracked for this paper; the generated
validator summary above is the current assumption-provenance status. Source
model hypotheses are visible in the theorem statements rather than treated as
additional assumptions.

## 13. Displayed Formula Provenance
Displayed and source-defining formulas are tracked through the paper-facing rows in `PaperInterface.lean` and the current statement-match sidecars. This report pass found no standalone formula-provenance issue beyond any source notes already listed above.

## 14. Library Lift Pass
No additional reusable library extraction was needed in this report pass.

## 15. DAG Audit
`DependencyDAG.tex` uses the shared DAG preamble and records the PAV Lemma C.1
path, filled-seat STV source semantics, STV rounding, and Proposition 1 as
formalized. `DependencyDAG.pdf` was regenerated from `DependencyDAG.tex` after
the closeout DAG update and visually inspected for node/label overlap and
arrow-through-text issues. The DAG covers the source-result clusters recorded
in the source inventory: Proposition 1 and Lemma C.1.

## 16. Validation Checks

<!-- BEGIN GENERATED LLM-AS-JUDGE RESULTS -->
### LLM-as-Judge Results
- Source coverage (`audit/paper_coverage_llm.json`): 19 covered.
- Statement match (`audit/statement_match_llm.json`): 19 matches.
- Lean-to-TeX translations (`audit/lean_to_tex_llm.json`): 19 row translations generated from Lean statements.
- Assumption provenance (`audit/assumption_match_llm.json`): no rows.
- Source-record classification (`audit/source_record_match_llm.json`): 2 proved_from_primitives, 2 validated_source_assumption.
- Source-record structural audit (`audit/source_record_audit.json`): 19 review rows, 4 boundary inputs, 0 recursion failures.
- Review-surface audit (`audit/review_surface_llm.json`): passes over 19 review rows.
- Holistic source-first audit (`docs/AGENT_SOURCE_AUDIT.md`): PASS.
- DAG/source/source-json audit (`docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`): PASS.
<!-- END GENERATED LLM-AS-JUDGE RESULTS -->

The review dashboard sidecars are current for the compact 19-row surface:
statement translation, statement match, paper coverage, source-to-Lean, and
assumption/source-record provenance prechecks all report no missing, stale, or
flagged items.

### Validation Commands
- `lake build GGRS26CombattingGerrymanderingRCV`
- `lake build EconCSLib.SocialChoice.Voting.STV.SolidCoalition`
- `python3 scripts/review_dashboard.py --paper GGRS26CombattingGerrymanderingRCV --statement-precheck`
- `python3 scripts/review_dashboard.py --paper GGRS26CombattingGerrymanderingRCV --paper-coverage-precheck`
- `python3 scripts/review_dashboard.py --paper GGRS26CombattingGerrymanderingRCV --source-to-lean-precheck`
- `python3 scripts/review_dashboard.py --paper GGRS26CombattingGerrymanderingRCV --assumption-precheck`
- `latexmk -pdf DependencyDAG.tex`
- `python3 scripts/audit_repository.py --paper GGRS26CombattingGerrymanderingRCV --paper-closeout --include-active --info-limit 0`

## 17. Paper Definitions Checked
No separate generated definitions table was recorded in this report refresh. The paper-facing definition rows are tracked in `PaperInterface.lean` and the statement validator sidecars.

## 18. Named Theorem Statements Checked
No separate generated theorem table was recorded in this report refresh. Named theorem endpoints are tracked in `PaperInterface.lean`, `status.json`, and the statement validator sidecars.

## 19. Paper-Facing Statement Validator Ledger
Current model-validator sidecars are the source of truth for timestamped rows. Model review has 19 matches across 19 rows. Human dashboard review has 0/19 saved entries, with 0 stale rows and 0 human mismatches.
