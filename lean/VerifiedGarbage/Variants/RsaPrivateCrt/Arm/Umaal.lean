module

public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.Arm.Umaal

/-!
# `vg_rsa_private_crt` on ARMv7: with `umaal`

A variant of `RsaPrivateCrt` on ARMv7 (see `TCB/Emit.lean`):
`vg_rsa_private_crt_umaal`, the baseline's code with each Montgomery row's
word steps by one `umaal` each, checked with the baseline's
`vg_rsa_public_precompute` and `vg_rsa_public_precomputed_checked`. It
needs the CPU feature `umaal`.
-/

@[expose] public section

namespace VG.Variants.RsaPrivateCrt.Arm.Umaal

def variant : Proof.Rsa.Arm.CrtImpl := Proof.Variants.RsaPrivateCrt.Arm.Umaal.variant

end VG.Variants.RsaPrivateCrt.Arm.Umaal
