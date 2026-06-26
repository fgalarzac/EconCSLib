/-!
# Stochastic Subgradient Method Boundary

This module records the current library-level boundary for stochastic
subgradient method convergence.

The intended future replacement is a concrete theorem with finite-dimensional
process hypotheses, step-size conditions, subgradient/noise/bias assumptions,
and an almost-sure convergence conclusion.  Until that reusable theorem is
proved in the library, papers may route theorem endpoints whose remaining proof
debt has been reduced to SSGM convergence through this single audited boundary
predicate.
-/

namespace EconCSLib
namespace Optimization

/--
Library-level marker for consequences whose remaining unformalized ingredient
is stochastic subgradient method convergence.

This is intentionally an `abbrev`, not a primitive postulate: the consequence
still has to be supplied as an explicit assumption at the paper boundary.  The
value of this declaration is provenance control: papers should depend on one
named SSGM boundary instead of accumulating many theorem-specific proof
assumptions.
-/
abbrev SSGMConvergenceBoundary (consequence : Prop) : Prop :=
  consequence

/-- Eliminator for a consequence routed through the SSGM convergence boundary. -/
theorem SSGMConvergenceBoundary.elim {consequence : Prop}
    (h : SSGMConvergenceBoundary consequence) : consequence :=
  h

end Optimization
end EconCSLib
