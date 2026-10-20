module

public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.AArch64.Base

/-!
# `vg_rsa_private_crt` on AArch64: the baseline

A variant of `RsaPrivateCrt` on AArch64 (see `TCB/Emit.lean`):
`vg_rsa_private_crt`, checked with `vg_rsa_public_precompute` and
`vg_rsa_public_precomputed_checked`. Its callers keep their plain names.
-/

@[expose] public section

namespace VG.Variants.RsaPrivateCrt.AArch64.Base

open VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64

def variant : Proof.Rsa.AArch64.CrtImpl := Proof.Variants.RsaPrivateCrt.AArch64.Base.variant

end VG.Variants.RsaPrivateCrt.AArch64.Base
