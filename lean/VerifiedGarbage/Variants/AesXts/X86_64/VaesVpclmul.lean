module

public import VerifiedGarbage.Proof.AesXts.X86_64.Variant

/-!
# XTS-AES of whole blocks on x86-64: in one pass, with VAES and VPCLMULQDQ

A variant of `AesXts` on x86-64 (see `TCB/Emit.lean`): `vg_aes_xts_encrypt_vaes_vpclmul` and `vg_aes_xts_decrypt_vaes_vpclmul`, which need VAES, VPCLMULQDQ and AVX2 (and AES-NI and AVX).
-/

@[expose] public section

namespace VG.Variants.AesXts.X86_64.VaesVpclmul

def variant : Proof.AesXts.X86_64.XtsImpl := .vaesVpclmul

end VG.Variants.AesXts.X86_64.VaesVpclmul
