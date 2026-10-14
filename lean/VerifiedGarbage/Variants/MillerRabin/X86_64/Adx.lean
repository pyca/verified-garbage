module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
public import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdxMont

/-! # The BMI2/ADX shared Miller–Rabin round -/

@[expose] public section

namespace VG.Variants.MillerRabin.X86_64.Adx

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64

def variant : RoundImpl where
  mont := Mont.fnAdx
  mxSafe := by decide +kernel
  spSafe := by decide +kernel
  suffix := "_adx"
  features := ["bmi2", "adx"]

end VG.Variants.MillerRabin.X86_64.Adx
