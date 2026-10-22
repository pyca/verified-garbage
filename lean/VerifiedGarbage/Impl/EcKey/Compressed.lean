module

public import VerifiedGarbage.Impl.EcKey.Compressed.Root
public import VerifiedGarbage.Spec.EcKey.Compressed

/-! # Functional coordinate recovery

This decoder supplies the common refinement target for the machine-code
implementations. The root method is curve-specific; parsing, canonical
coordinates, root checking and parity selection are shared.
-/

@[expose] public section

namespace VG.Impl.EcKey.Compressed

open Spec.Weierstrass

def decode (C : Curve) (root : Fe C → Fe C) (bs : List Byte) : Option (Point C) :=
  if bs.length = C.len + 1 then
    match bs.head? with
    | none => none
    | some tag =>
      if tag = 2 ∨ tag = 3 then
        let x := ofBytes (bs.drop 1)
        if hx : x < C.p then
          let x : Fe C := ⟨x, hx⟩
          let rhs := x * x * x + Fin.ofNat C.p C.a * x + Fin.ofNat C.p C.b
          (recoverRoot root rhs (tag.toNat % 2)).map (Point.affine x)
        else none
      else none
  else none

end VG.Impl.EcKey.Compressed
