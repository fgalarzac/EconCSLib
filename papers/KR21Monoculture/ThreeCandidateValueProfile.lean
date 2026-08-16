import KR21Monoculture.RUM

/-!
# Shared three-candidate value profile for KR21

The fixed profile used in the source iid-noise construction and in the named
three-score law is defined once here.  Keeping this object below either proof
route prevents law-transport arguments from relying on two independently
spelled but supposedly identical profiles.
-/

namespace KR21Monoculture

/-- The canonical value profile `(x1, x2, x3)` on the three-candidate type. -/
def threeCandidateValueProfile (x1 x2 x3 : ℝ) : Candidate 1 → ℝ :=
  fun c => if c = 0 then x1 else if c = 1 then x2 else x3

end KR21Monoculture
