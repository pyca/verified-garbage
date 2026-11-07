module

public import VerifiedGarbage.Proof.Variants.MillerRabin.X86_64.Ifma

/-! # The AVX512_IFMA shared Miller–Rabin round -/

@[expose] public section

namespace VG.Variants.MillerRabin.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64

def variant : RoundImpl := Proof.Variants.MillerRabin.X86_64.Ifma.variant

end VG.Variants.MillerRabin.X86_64.Ifma
