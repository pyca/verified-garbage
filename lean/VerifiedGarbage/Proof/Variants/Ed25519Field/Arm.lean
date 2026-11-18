module

/-! # The implementations of Ed25519's field (`Impl/Ed25519/Arm/MulFn.lean`) on 32-bit ARM

Its multiplication is by 16 × 16-bit products of its limbs, or by `umaal` on the limbs packed in
words (CPU feature `umaal`): `mulIn umaal` and `mulFn umaal`, proven for both
(`Proof/Ed25519/Arm/FieldProg.lean`). A function that multiplies in the field is emitted with each:
Ed25519's, and X25519's multiplication of the base point, which is by Ed25519's comb.
-/

@[expose] public section

namespace VG.Proof.Variants.Ed25519Field.Arm

/-- An implementation of the field: its `umaal` flag and its callers' suffix. -/
structure Variant where
  umaal : Bool
  suffix : String

def base : Variant := ⟨false, ""⟩

def umaal : Variant := ⟨true, "_umaal"⟩

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants : List Variant := [umaal, base]

end VG.Proof.Variants.Ed25519Field.Arm
