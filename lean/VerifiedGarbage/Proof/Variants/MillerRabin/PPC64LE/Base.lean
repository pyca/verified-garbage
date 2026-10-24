module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Backend
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Verified

/-! # The verified baseline prepared round on PPC64LE -/

@[expose] public section
namespace VG.Proof.Variants.MillerRabin.PPC64LE.Base
open VG VG.PPC64LE VG.Proof.MillerRabin.PPC64LE

def variant : RoundImpl where
  code := Impl.StackScratch.PPC64LE.withStackScratch 176 .r5 Impl.MillerRabin.PPC64LE.round
  verified := round_verified
  stack := by decide +kernel
  suffix := ""
  features := []

end VG.Proof.Variants.MillerRabin.PPC64LE.Base
