/-!
# Non-Authoritative Paper Interface Template

This legacy template intentionally contains no mathematical declarations. Do
not copy it to start a formalization. Run
`python3 scripts/paper_contribution.py new --help` from the repository root and
use the generated paper scaffold instead.

For every generated paper, `PaperInterface.lean` is the sole paper-facing Lean
surface and the compact file a reviewer reads to check the audited source
definitions and named results. Keep it in source order and keep assumptions
visible in theorem signatures.

- Put proofs and internal helpers in `MainTheorems.lean` or lower modules.
- Use `ProofInterface.lean` or `AuditInterface.lean` only when a compact proof-
  support surface is genuinely useful. Those files are not alternative paper-
  facing surfaces and must not carry source-coverage credit.
- Do not create `PostPaperAudit.lean` or another competing paper-facing ledger.
- Do not add placeholder propositions or trivial theorems. Generate exact
  source-shaped statement skeletons through the contribution workflow.
-/
