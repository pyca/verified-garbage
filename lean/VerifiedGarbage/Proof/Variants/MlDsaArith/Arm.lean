module

/-! # The implementations of `MlDsaArith` on 32-bit ARM

The transforms `NTT` and `NTT⁻¹` (`Impl/MlDsa/Arm/Arith/Ntt.lean`) multiply by a zeta with `mul` and
`mla` alone, or with `umaal` (CPU feature `umaal`): `ntt um` and `nttInv um`, proven for both
(`Proof/MlDsa/Arm/Arith/Ntt.lean`, `NttInv.lean`). A function that calls them is emitted with each.
-/

@[expose] public section

namespace VG.Proof.Variants.MlDsaArith.Arm

/-- An implementation of the transforms: its `umaal` flag and its callers' suffix. -/
structure Variant where
  um : Bool
  suffix : String

def base : Variant := ⟨false, ""⟩

def umaal : Variant := ⟨true, "_umaal"⟩

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants : List Variant := [umaal, base]

end VG.Proof.Variants.MlDsaArith.Arm
