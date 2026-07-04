import KR21Monoculture.AuditInterface

/-!
# Human-Facing Paper Interface: Algorithmic Monoculture and Social Welfare

This is the compact entrypoint for human readers.

The row-level dashboard and LLM-as-judge review surface is
`AuditInterface.lean`. That file preserves the checked declarations listed in
`status.json` `review_surface.include_names`; this file keeps
`PaperInterface.lean` as the stable paper-facing module without duplicating the
large audit ledger.

For source-to-Lean statement review, use the rows named in `status.json` and
implemented in `AuditInterface.lean`. For orientation, start with the final
validation report and dependency DAG.
-/
