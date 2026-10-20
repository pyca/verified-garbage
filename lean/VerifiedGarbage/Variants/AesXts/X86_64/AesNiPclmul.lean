module

public import VerifiedGarbage.Proof.AesXts.X86_64.Variant

/-!
# XTS-AES of whole blocks on x86-64: in one pass, with AES-NI and PCLMULQDQ

A variant of `AesXts` on x86-64 (see `TCB/Emit.lean`): `vg_aes_xts_encrypt_aesni_pclmul` and `vg_aes_xts_decrypt_aesni_pclmul`, which need AES-NI, AVX and PCLMULQDQ.
-/

@[expose] public section

namespace VG.Variants.AesXts.X86_64.AesNiPclmul

def variant : Proof.AesXts.X86_64.XtsImpl := .aesniPclmul

end VG.Variants.AesXts.X86_64.AesNiPclmul
