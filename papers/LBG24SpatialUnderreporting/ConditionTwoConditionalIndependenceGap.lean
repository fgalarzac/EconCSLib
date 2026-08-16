import Mathlib.Tactic

/-!
# Finite conditional-independence gap behind LBG Appendix Theorem 2

The printed Conditions 1--2 give marginal conditional kernels for the selected
start and endpoint, together with endpoint independence from the selected start
given the first report.  The proof of Eq. (8), however, conditions on a richer
report history as well as the selected start.  This file records a checked
finite witness that the corresponding marginal facts do not imply the needed
history-level conditional independence.

It is deliberately a two-bit probability-table argument, not a replacement
for the paper's Poisson process.  Taking the first-report time deterministic
and product-coupling this table to any Poisson path preserves the relevant
logical gap: independent marginal endpoint kernels need not stay independent
after both the selected start and a richer history are revealed.
-/

namespace LBG24SpatialUnderreporting

/-- A four-atom uniform sample space: `(selectedStart, preEndHistory)`. -/
abbrev ConditionTwoGapAtom := Bool × Bool

/-- The endpoint bit is the XOR of the selected-start and history bits. -/
def conditionTwoGapEndpoint (ω : ConditionTwoGapAtom) : Bool :=
  ω.1.xor ω.2

/-- Number of atoms with prescribed start and endpoint values. -/
def conditionTwoGapStartEndpointCard (start endpoint : Bool) : ℕ :=
  (Finset.univ.filter fun ω : ConditionTwoGapAtom =>
    ω.1 == start && conditionTwoGapEndpoint ω == endpoint).card

/-- Number of atoms with prescribed selected-start and history values. -/
def conditionTwoGapStartHistoryCard (start history : Bool) : ℕ :=
  (Finset.univ.filter fun ω : ConditionTwoGapAtom =>
    ω.1 == start && ω.2 == history).card

/-- Number of atoms with prescribed history and endpoint values. -/
def conditionTwoGapHistoryEndpointCard (history endpoint : Bool) : ℕ :=
  (Finset.univ.filter fun ω : ConditionTwoGapAtom =>
    ω.2 == history && conditionTwoGapEndpoint ω == endpoint).card

/-- Number of atoms with the full `(start, history, endpoint)` specification. -/
def conditionTwoGapJointCard (start history endpoint : Bool) : ℕ :=
  (Finset.univ.filter fun ω : ConditionTwoGapAtom =>
    ω.1 == start && ω.2 == history && conditionTwoGapEndpoint ω == endpoint).card

/-- In the uniform four-atom model, the endpoint is uniform after fixing only
the selected start.  This is the finite-table analogue of endpoint/start
marginal independence. -/
theorem conditionTwoGap_endpoint_uniform_given_start :
    ∀ start endpoint : Bool,
      conditionTwoGapStartEndpointCard start endpoint = 1 := by
  decide

/-- The selected start and the history bit are independent in this uniform
four-atom table.  This is the finite analogue of the future-tail independence
portion of Condition 1. -/
theorem conditionTwoGap_start_independent_of_history :
    ∀ start history : Bool,
      conditionTwoGapStartHistoryCard start history = 1 := by
  decide

/-- In the same model, the endpoint is uniform after fixing only the report
history.  Thus a rate-free endpoint kernel indexed by the history can hold. -/
theorem conditionTwoGap_endpoint_uniform_given_history :
    ∀ history endpoint : Bool,
      conditionTwoGapHistoryEndpointCard history endpoint = 1 := by
  decide

/-- Once both selected start and report history are exposed, the endpoint is
deterministic.  At this atom it is false. -/
theorem conditionTwoGap_joint_endpoint_false :
    conditionTwoGapJointCard false false false = 1 := by
  decide

/-- The other endpoint value has zero conditional mass after exposing the
same selected start and history. -/
theorem conditionTwoGap_joint_endpoint_true :
    conditionTwoGapJointCard false false true = 0 := by
  decide

/-- Therefore the two marginal kernel facts above do not entail the
history-and-start conditional endpoint kernel used in the Eq. (8) chain-rule
step.  The displayed unequal fiber counts are the finite witness. -/
theorem conditionTwoGap_marginals_do_not_determine_joint_kernel :
    conditionTwoGapJointCard false false false ≠
      conditionTwoGapJointCard false false true := by
  decide

end LBG24SpatialUnderreporting
