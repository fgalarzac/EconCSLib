import DGD26AdmissionsPredictability.AuditInterface

namespace DGD26AdmissionsPredictability

open EconCSLib.FiniteChoice

variable {α : Type*} [DecidableEq α]

/-- The paper's recursive queue composition on the remaining applicant pool. -/
def sequentialCompositionSource : List (PaperChoiceRule α) → PaperChoiceRule α
  | [] => fun _ => ∅
  | C :: Cs => fun X =>
      let chosen := C X
      chosen ∪ sequentialCompositionSource Cs (X \ chosen)

/-- The paper's feasible, capacity-filling, objective-optimal assignment model. -/
def lapModel {σ : Type*} [DecidableEq σ] [Fintype σ]
    (X : Finset α) (w : α → σ → ℝ) (A : LAP.Assignment α σ) : Prop :=
  paper_definition_lap_assignment_feasible X A ∧
    paper_definition_lap_capacity_filling X A ∧
      paper_definition_lap_objective_optimal X w A

end DGD26AdmissionsPredictability
