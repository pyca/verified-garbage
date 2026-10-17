module

public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.Arm.Base

/-!
# `vg_rsa_private_crt` on ARMv7: the baseline

A variant of `RsaPrivateCrt` on ARMv7 (see `TCB/Emit.lean`):
`vg_rsa_private_crt`, checked with `vg_rsa_public_precompute` and
`vg_rsa_public_precomputed_checked`. Its callers keep their plain names.
-/

@[expose] public section

namespace VG.Variants.RsaPrivateCrt.Arm.Base

def variant : Proof.Rsa.Arm.CrtImpl := Proof.Variants.RsaPrivateCrt.Arm.Base.variant

end VG.Variants.RsaPrivateCrt.Arm.Base
