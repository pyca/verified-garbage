module

public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.X86_64.Adx

/-!
# `vg_rsa_private_crt` on x86-64: with BMI2 and ADX

A variant of `RsaPrivateCrt` on x86-64 (see `TCB/Emit.lean`):
`vg_rsa_private_crt_adx`, checked with `vg_rsa_public_precompute_adx` and
`vg_rsa_public_precomputed_checked_adx`, all three by calls of
`vg_rsa_mont_mul_adx`, which needs BMI2 and ADX; the first exponentiates by
windows of 5 bits (`Crt.expLoop5`), reading its table of 32 powers with AVX2
(`Crt.tabSelectV`).
-/

@[expose] public section

namespace VG.Variants.RsaPrivateCrt.X86_64.Adx

open VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

def variant : CrtImpl := Proof.Variants.RsaPrivateCrt.X86_64.Adx.variant

end VG.Variants.RsaPrivateCrt.X86_64.Adx
