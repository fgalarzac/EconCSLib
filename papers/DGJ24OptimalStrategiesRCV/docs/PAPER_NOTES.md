# Optimal Strategies in Ranked-Choice Voting Formalization Notes

This is a lightweight handoff document for source-to-Lean mapping.

- Namespace: `DGJ24OptimalStrategiesRCV`
- Official URL: https://arxiv.org/abs/2407.13661
- Source PDF: `source.pdf`
- Local source text cache, if generated: `source.txt` (ignored by Git in public workspaces)

## Formalization checklist

- [ ] Full named-result inventory copied to the README theorem table.
- [ ] DAG graph includes all required paper-stage nodes and dependencies.
- [ ] README status and remaining-assumption notes match proof artifacts.
- [ ] Post-formalization library elevation pass completed: reusable proof
      results, techniques, and primitives were moved into `EconCSLib` when
      local/low-risk, or recorded with destination modules in the final report.
- [ ] Recursive provenance audit completed with
      `python3 scripts/audit_repository.py --include-active --library-premise-audit --info-limit 0 --write-report docs/RECURSIVE_PROVENANCE_AUDIT_<date>.md`;
      all findings for this paper are resolved or explicitly recorded as
      partial/conditional boundaries.
- [ ] Final status review completed before publishing.

## Notes

- Date reviewed: 2026-06-29 stopping point.
- Last theorem row formalized:
  `paper_proposition3_4_sequence_reduction_sound_and_quadratic_runtime_from_algorithm7_source_loops`.
- Outstanding assumptions / caveats: Proposition 3.4 now has reusable
  current-prefix ready-set constructors for Predict-Wins selections and an
  ordered-loop-prefix constructor for Predict-Losses.  The remaining Algorithm
  7 source-model work is proving concrete Predict-Wins selections belong to the
  prefix ready set and proving the Predict-Losses loop prefix is an initial
  losing segment for each feasible sequence; broader Theorem 3.1/3.2, Section
  5, and Appendix B.2 source constructors remain visible partial boundaries.
- Reusable library elevation candidates: the current-prefix ready-set
  constructors in `Voting.Ballot` are now shared library tooling; add further
  source-loop combinators only if DGJ26 needs a different traversal shape.
