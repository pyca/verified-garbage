module

public import VerifiedGarbage.Proof.MillerRabin.X86.Backend

/-! # The baseline i686 prepared-round variant -/

@[expose] public section
namespace VG.Proof.Variants.MillerRabin.X86.Base
open VG.Proof.MillerRabin.X86

def variant : RoundImpl where
  code := VG.Impl.MillerRabin.X86.code
  verified := round_verified
  stack := Nat.le_of_eq round_stack
  spSafe := by decide
  suffix := ""
  features := []

end VG.Proof.Variants.MillerRabin.X86.Base
