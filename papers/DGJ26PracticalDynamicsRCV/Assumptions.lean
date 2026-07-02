import DGJ26PracticalDynamicsRCV.MainTheorems

/-!
# Paper Assumptions: Simpler Than You Think: The Practical Dynamics of Ranked Choice Voting

This file is the only paper-local place for assumptions that are not derived in
Lean. Keep it small. Each declaration must be explicitly stated by the paper,
listed in `status.json` `review_surface.assumption_names`, and judged in
`assumption_match_llm.json` as a true source/model assumption rather than a
proof convenience.

Use `-- audit-premise: <exact Lean binder>` comments to route hidden theorem
premises to an approved assumption declaration when the audit reports an exact
binder string.

## Paper Assumptions

No paper-local assumptions are needed for the current ballot-robustness
interface rows. Future SmartAllocation, candidate-removal, or empirical audit
claims should add explicit assumptions here only when a premise is stated in the
source and not derived in Lean.
-/

namespace DGJ26PracticalDynamicsRCV

end DGJ26PracticalDynamicsRCV
