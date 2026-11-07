module

public import VerifiedGarbage.Proof.Variants.MillerRabin.X86_64.Adx
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Ifma.Round
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Ifma.CT

/-!
# The AVX512_IFMA shared Miller–Rabin round: the variant's code and proofs

The variant `VG.Variants.MillerRabin.X86_64.Ifma.variant`
(`Variants/MillerRabin/X86_64/Ifma.lean`): the BMI2/ADX arithmetic for the
callers, and the round of `Impl/MillerRabin/X86_64/Ifma.lean`, in radix
`2⁵²` for 2048-, 3072- and 4096-bit candidates and the ADX round otherwise.
-/

@[expose] public section

namespace VG.Proof.Variants.MillerRabin.X86_64.Ifma

open VG VG.X86_64 VG.Proof.MillerRabin.X86_64

def variant : RoundImpl :=
  { Adx.arith with
    code := Impl.MillerRabin.X86_64.Ifma.code Adx.arith.mm
    spSafe := Proof.MillerRabin.X86_64.Ifma.code_spSafe Adx.arith (by decide +kernel)
    depth := Proof.MillerRabin.X86_64.Ifma.code_depth Adx.arith (by decide +kernel)
    ctl := Proof.MillerRabin.X86_64.Ifma.code_ctl Adx.arith
    correct := Proof.MillerRabin.X86_64.Ifma.code_correct Adx.arith
    ct := Proof.MillerRabin.X86_64.Ifma.code_ct Adx.arith
    suffix := "_ifma"
    features := ["avx", "avx512f", "avx512ifma", "avx512vl", "bmi2", "adx"]
    arithFeatures := ["bmi2", "adx"] }

end VG.Proof.Variants.MillerRabin.X86_64.Ifma
