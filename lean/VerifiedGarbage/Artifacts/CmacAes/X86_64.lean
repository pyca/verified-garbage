import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.CmacAes.X86_64.AesNi

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

namespace VG.Artifacts.CmacAes.X86_64

def artifacts : List Artifact := [
  { Spec.Cmac.aesUpdateApi with
    name := Spec.Cmac.aesUpdateApi.name ++ "_aesni_cbc"
    target := X86_64.target
    doc := Spec.Cmac.aesUpdateApi.doc (notes := [
      "This implementation keeps the round keys in SSE registers and the chaining value in `xmm0` \
      across all blocks: it loads them once, and stores the chaining value once. The first round \
      key is folded into the chaining value and the last one, so each block is one `pxor`, the \
      `aesenc` rounds and one `aesenclast`; the number of rounds is selected once. It uses no \
      stack and does not use `scratch`."])
    code := Impl.CmacAes.X86_64.AesNi.update
    contract := Spec.Cmac.aesUpdateContract X86_64.abi
    verified := Proof.CmacAes.X86_64.AesNi.verified
    spSafe := Code.all_of_allInstrs (by decide +kernel)
    features := ["aes"] }]

end VG.Artifacts.CmacAes.X86_64
