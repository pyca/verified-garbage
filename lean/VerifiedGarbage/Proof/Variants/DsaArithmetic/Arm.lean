module

/-! # The implementations of DSA's arithmetic (`Impl/Mont/Arm/Dynamic.lean`) on 32-bit ARM

Its Montgomery multiplication is on 16-bit digits, or on words by `umaal` (CPU feature `umaal`):
`mul umaal`, proven for both (`Proof/Mont/Arm/Dyn/Context.lean`). A function that multiplies is
emitted with each.
-/

@[expose] public section

namespace VG.Proof.Variants.DsaArithmetic.Arm

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

end VG.Proof.Variants.DsaArithmetic.Arm
