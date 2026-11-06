module

public import VerifiedGarbage.Spec.Ed25519
public import VerifiedGarbage.TCB.Artifact

/-!
# RFC 8032's point doubling, in its stated order

Not trusted: a definition the proofs of Ed25519's point doublings state what
they compute with, and check against the specification.

`pointDouble` is the doubling formula of RFC 8032, §5.1.4, on points of
edwards25519 in extended coordinates (`Point`), its operations in the order
the RFC states them: the double `[2]p`, which does not read `p.T`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.Point64

open VG.Spec VG.Spec.Ed25519

open X25519 (P Fe)

/-- The doubling formula of RFC 8032, §5.1.4, in its stated order: the
double `[2]p` of a point in extended coordinates, which does not read `p.T`. -/
def pointDouble (p : Point) : Point :=
  let a := p.X * p.X
  let b := p.Y * p.Y
  let c := 2 * (p.Z * p.Z)
  let h := a + b
  let e := h - (p.X + p.Y) * (p.X + p.Y)
  let g := a - b
  let f := c + g
  ⟨e * f, g * h, f * g, e * h⟩

end VG.Proof.Ed25519.Point64
