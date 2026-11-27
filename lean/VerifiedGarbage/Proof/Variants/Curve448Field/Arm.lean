module

/-! # The implementations of `Curve448Field` on 32-bit ARM

The field's multiplication (`Impl/X448/Arm.lean`) is by 16 × 16-bit products of its limbs, or by
`umaal` on the limbs packed in words (CPU feature `umaal`): `mulFn um`, proven for both
(`Proof/X448/Arm/Env.lean`). A function that multiplies in the field is emitted with each.
-/

@[expose] public section

namespace VG.Proof.Variants.Curve448Field.Arm

/-- An implementation of the field: its `umaal` flag and its callers' suffix. -/
structure Variant where
  um : Bool
  suffix : String

def base : Variant := ⟨false, ""⟩

def umaal : Variant := ⟨true, "_umaal"⟩

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants : List Variant := [umaal, base]

end VG.Proof.Variants.Curve448Field.Arm
