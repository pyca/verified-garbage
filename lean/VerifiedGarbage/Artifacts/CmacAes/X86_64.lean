module

public import VerifiedGarbage.Proof.CmacAes.X86_64.AesNi
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# AES-CMAC's chaining with AES-NI on x86-64

`vg_cmac_aes_update_aesni_cbc`, the variant of `vg_cmac_aes_update` that
keeps the round keys and the chaining value in registers across blocks.
The other x86-64 CMAC functions are generic over `vg_aes_ctr32`
(`Generic/AesCtr32/X86_64/CmacAes.lean`), and the callers of
`vg_cmac_aes_update` over its implementations
(`Generic/CmacAesUpdate/X86_64/`), this one among them
(`Variants/CmacAesUpdate/X86_64/AesNiCbc.lean`).
-/

@[expose] public section

namespace VG.Artifacts.CmacAes.X86_64

def artifacts : List Artifact := [
  Spec.Cmac.aesUpdateApi.artifact X86_64.target {
    suffix := "_aesni_cbc"
    notes := [
      "This implementation keeps the round keys in SSE registers and the chaining value in `xmm0` \
      across all blocks: it loads them once, and stores the chaining value once. The first round \
      key is folded into the chaining value and the last one, so each block is one `pxor`, the \
      `aesenc` rounds and one `aesenclast`; the number of rounds is selected once. It uses no \
      stack and does not use `scratch`."]
    code := Impl.CmacAes.X86_64.AesNi.update
    verified := Proof.CmacAes.X86_64.AesNi.verified
    features := ["aes"] }]

end VG.Artifacts.CmacAes.X86_64
