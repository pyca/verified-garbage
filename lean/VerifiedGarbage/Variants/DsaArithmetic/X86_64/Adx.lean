module

public import VerifiedGarbage.Proof.Variants.DsaArithmetic.X86_64.Adx

/-! # BMI2/ADX Montgomery arithmetic for DSA -/

@[expose] public section

namespace VG.Variants.DsaArithmetic.X86_64.Adx

open VG VG.X86_64 VG.Proof.Dsa.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

def variant : Backend := Proof.Variants.DsaArithmetic.X86_64.Adx.variant

end VG.Variants.DsaArithmetic.X86_64.Adx
