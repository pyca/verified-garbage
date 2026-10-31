module

public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.X86_64.Ifma

/-! # `vg_rsa_private_crt` on x86-64: with AVX512_IFMA -/

@[expose] public section

namespace VG.Variants.RsaPrivateCrt.X86_64.Ifma

open VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

def variant : CrtImpl := Proof.Variants.RsaPrivateCrt.X86_64.Ifma.variant

end VG.Variants.RsaPrivateCrt.X86_64.Ifma
