import DGJ24OptimalStrategiesRCV.MainTheorems

/-!
# Paper Assumptions: Optimal Strategies in Ranked-Choice Voting

This file is the only paper-local place for assumptions that are not derived in
Lean. DGJ24 currently has no paper-local assumption declarations: the
structure-partition and direct-STV/constraint agreement inputs are
source-facing predicates in `PaperInterface.lean`, and the consequences are
proved in `MainTheorems.lean`.

Use `-- audit-premise: <exact Lean binder>` comments to route hidden theorem
premises to an approved assumption declaration when the audit reports an exact
binder string.

## Paper Assumptions

None.
-/

namespace DGJ24OptimalStrategiesRCV

end DGJ24OptimalStrategiesRCV
