/-!
# Non-Authoritative Assumptions Template

This legacy template intentionally declares no assumptions. Do not copy it to
start a formalization. Run `python3 scripts/paper_contribution.py new --help`
from the repository root and use the generated paper scaffold instead.

In a generated paper, `Assumptions.lean` is the only paper-local place for
paper-facing premises that are not derived in Lean. Every declaration there
must be source-backed, listed in `status.json` `review_surface.assumption_names`,
and reviewed through the configured assumption sidecar. Never add a trivial
placeholder proposition or a proof-convenience assumption merely to make a
paper-facing theorem compile.
-/
