module

public import VerifiedGarbage.Proof.MillerRabin.X86.Backend
public import VerifiedGarbage.Proof.MillerRabin.X86.Verified
public import VerifiedGarbage.Proof.MillerRabin.X86.Baseline

/-! # The verified baseline prepared round on i686 -/

@[expose] public section
namespace VG.Proof.Variants.MillerRabin.X86.Base
open VG VG.Proof.MillerRabin.X86

def variant : RoundImpl where
  code := Impl.MillerRabin.X86.code montName montCode
  verified := VG.Proof.MillerRabin.X86.verified
  noSp := code_noSp
  spSafe := by decide +kernel
  stack := code_stack
  suffix := ""
  features := []

end VG.Proof.Variants.MillerRabin.X86.Base
