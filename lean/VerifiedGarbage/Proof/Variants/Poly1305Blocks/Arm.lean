module

/-! # The implementations of Poly1305's arithmetic (`Impl/Poly1305/Arm.lean`) on 32-bit ARM

Its multiplication is in radix `2¹³`, with `mul`, or in radix `2³²`, with `umaal` (CPU feature
`umaal`): `blocks umaal`, `update umaal` and `finalize umaal`, proven for both
(`Proof/Poly1305/Arm/Finalize.lean`). A function that absorbs blocks is emitted with each.
-/

@[expose] public section

namespace VG.Proof.Variants.Poly1305Blocks.Arm

/-- An implementation of the arithmetic: its `umaal` flag and its callers' suffix. -/
structure Variant where
  umaal : Bool
  suffix : String

def base : Variant := ⟨false, ""⟩

def umaal : Variant := ⟨true, "_umaal"⟩

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants : List Variant := [umaal, base]

end VG.Proof.Variants.Poly1305Blocks.Arm
