import VerifiedGarbage.Spec.Ed25519

/-!
# The dedicated doubling's formula

`dblPoint`, apart from the group law it is proven against (`Group/Double.lean`), so that
code computing it need not import the group's algebra.
-/

namespace VG.Proof.Ed25519

open Spec.Ed25519 (Point)

/-- `E = 2XY`, `G = Y² - X²`, `F = 2Z² - G`, `H = X² + Y²`, and
`(EF, GH, FG, EH)`. -/
def dblPoint (p : Point) : Point :=
  ⟨(p.X * p.Y + p.X * p.Y) * (p.Z * p.Z + p.Z * p.Z - (p.Y * p.Y - p.X * p.X)),
    (p.Y * p.Y - p.X * p.X) * (p.X * p.X + p.Y * p.Y),
    (p.Z * p.Z + p.Z * p.Z - (p.Y * p.Y - p.X * p.X)) * (p.Y * p.Y - p.X * p.X),
    (p.X * p.Y + p.X * p.Y) * (p.X * p.X + p.Y * p.Y)⟩

end VG.Proof.Ed25519
