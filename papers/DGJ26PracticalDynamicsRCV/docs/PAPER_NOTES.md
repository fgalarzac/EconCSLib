# Simpler Than You Think: The Practical Dynamics of Ranked Choice Voting Formalization Notes

This is a lightweight handoff document for source-to-Lean mapping.

- Namespace: `DGJ26PracticalDynamicsRCV`
- Official URL: https://link.springer.com/article/10.1007/s42001-026-00470-7
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
- Last theorem rows formalized include
  `paper_proposition2_multi_round_closeout_from_algorithmA_count_test` and
  `paper_theorem2_2_algorithm4_exact_bounds_sound_and_quadratic_verification`.
- Outstanding assumptions / caveats: Algorithm A robust-output constructors
  and full extraction from concrete election runs remain open, including
  Theorem 2.1's source branch and Theorem 2.2's source pairwise inequalities;
  DGJ24 source constructors are upstream dependencies for the cleanest closeout
  path.
- Reusable library elevation candidates: only lift DGJ26-local constructors if
  they do not duplicate DGJ24 SmartAllocation or candidate-removal semantics.
