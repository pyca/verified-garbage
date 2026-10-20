module

public import VerifiedGarbage.Spec.Weierstrass.Point

/-! # secp256k1's instance of the shared point-operation API -/

@[expose] public section

namespace VG.Impl.Secp256k1

/-- Four 64-bit words per coordinate, using the existing generic point contract. -/
def point : Spec.Weierstrass.Point.Curve :=
  { curve := "secp256k1", p := Spec.Secp256k1.p, k := 4, desc := "secp256k1" }

end VG.Impl.Secp256k1
