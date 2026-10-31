module

public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.X86_64.Base

/-! # `vg_rsa_private_crt` on x86-64: the baseline -/

@[expose] public section

namespace VG.Variants.RsaPrivateCrt.X86_64.Base

open VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

def variant : CrtImpl := Proof.Variants.RsaPrivateCrt.X86_64.Base.variant

end VG.Variants.RsaPrivateCrt.X86_64.Base
