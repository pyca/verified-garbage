module

public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.X86_64.Ifma

/-!
# `vg_rsa_private_crt` on x86-64: with AVX512_IFMA

A variant of `RsaPrivateCrt` on x86-64 (see `TCB/Emit.lean`):
`vg_rsa_private_crt_ifma`, checked with `vg_rsa_public_precompute_adx` and
`vg_rsa_public_precomputed_checked_adx` (there is no public operation with
AVX512_IFMA), which need AVX512_IFMA, AVX512F, AVX512VL, AVX, BMI2 and ADX;
its Montgomery multiplications outside the vector code are calls of
`vg_rsa_mont_mul_adx`.
-/

@[expose] public section

namespace VG.Variants.RsaPrivateCrt.X86_64.Ifma

open VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

def variant : CrtImpl := Proof.Variants.RsaPrivateCrt.X86_64.Ifma.variant

end VG.Variants.RsaPrivateCrt.X86_64.Ifma
