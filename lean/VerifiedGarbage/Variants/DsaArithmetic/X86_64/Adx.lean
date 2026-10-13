module

public import VerifiedGarbage.Proof.Dsa.X86_64.Backend
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT

/-! # BMI2/ADX Montgomery arithmetic for DSA -/

@[expose] public section

namespace VG.Variants.DsaArithmetic.X86_64.Adx
open VG VG.X86_64 VG.Proof.Dsa.X86_64 VG.Proof.Bignum.X86_64

def variant : Backend where
  mont := Mont.adx
  suffix := "_adx"
  features := ["bmi2", "adx"]
  signMx := by decide +kernel
  verifyMx := by decide +kernel
  signSp := Code.all_of_allInstrs (by decide +kernel)
  verifySp := Code.all_of_allInstrs (by decide +kernel)

end VG.Variants.DsaArithmetic.X86_64.Adx
