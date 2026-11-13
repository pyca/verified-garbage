module

/-! # The implementations of the RSA keys' inverse (`Impl/Rsa/Arm/Inverse.lean`) on 32-bit ARM

The inverse's batches add their terms by 16 × 16-bit products (`termB`), or by `umaal` (`termU`,
CPU feature `umaal`): `inverse um`, proven for both (`Proof/Rsa/Arm/InvLoop.lean`). A function
that runs the inverse is emitted with each.
-/

@[expose] public section

namespace VG.Proof.Variants.RsaInverse.Arm

/-- An implementation of the inverse: its `umaal` flag and its callers' suffix. -/
structure Variant where
  um : Bool
  suffix : String

def base : Variant := ⟨false, ""⟩

def umaal : Variant := ⟨true, "_umaal"⟩

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants : List Variant := [umaal, base]

end VG.Proof.Variants.RsaInverse.Arm
