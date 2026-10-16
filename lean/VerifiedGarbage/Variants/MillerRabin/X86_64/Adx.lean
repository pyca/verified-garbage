module

public import VerifiedGarbage.Proof.Variants.MillerRabin.X86_64.Adx

/-! # The BMI2/ADX shared Miller–Rabin round -/

@[expose] public section

namespace VG.Variants.MillerRabin.X86_64.Adx

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64

def variant : RoundImpl := Proof.Variants.MillerRabin.X86_64.Adx.variant

end VG.Variants.MillerRabin.X86_64.Adx
