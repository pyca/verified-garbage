import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Verified
import VerifiedGarbage.Proof.AesXts.X86_64.AesNi.Verified

/-!
# XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) on x86-64, in one pass

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. They are the variants `_vaes_vpclmul` and `_aesni_pclmul` of
`vg_aes_xts_encrypt` and `vg_aes_xts_decrypt` (whose instances for each
implementation of the block functions are in
`Generic/AesBlocks/X86_64/AesXts.lean`): they call nothing, and compute the
tweaks of eight blocks at a time with a carry-less multiplication, keeping
them in registers (`_vaes_vpclmul`) or in the scratch buffer
(`_aesni_pclmul`).

They write no stack; the 8 bytes are those of the shared precondition.
-/

namespace VG.Artifacts.AesXts.X86_64


def artifacts : List Artifact := [
  { Spec.Xts.aesEncryptApi with
    name := Spec.Xts.aesEncryptApi.name ++ "_vaes_vpclmul"
    target := X86_64.target
    doc := Spec.Xts.aesEncryptApi.doc (notes := [
      "This implementation reads each block once: it enciphers eight blocks at a time with VAES, " ++
      "their tweaks kept in registers and computed eight at a time with VPCLMULQDQ, and the rest with AES-NI."])
    code := Impl.AesXts.X86_64Vaes.encrypt
    contract := Spec.Xts.aesEncryptContract X86_64.abi 8
    stack := 8
    verified := Proof.AesXts.X86_64.Vaes.encrypt_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel)
    features := ["aes", "avx", "avx2", "vaes", "vpclmulqdq"] },
  { Spec.Xts.aesDecryptApi with
    name := Spec.Xts.aesDecryptApi.name ++ "_vaes_vpclmul"
    target := X86_64.target
    doc := Spec.Xts.aesDecryptApi.doc (notes := [
      "This implementation reads each block once: it deciphers eight blocks at a time with VAES, " ++
      "their tweaks kept in registers and computed eight at a time with VPCLMULQDQ, and the rest with AES-NI."])
    code := Impl.AesXts.X86_64Vaes.decrypt
    contract := Spec.Xts.aesDecryptContract X86_64.abi 8
    stack := 8
    verified := Proof.AesXts.X86_64.Vaes.decrypt_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel)
    features := ["aes", "avx", "avx2", "vaes", "vpclmulqdq"] },
  { Spec.Xts.aesEncryptApi with
    name := Spec.Xts.aesEncryptApi.name ++ "_aesni_pclmul"
    target := X86_64.target
    doc := Spec.Xts.aesEncryptApi.doc (notes := [
      "This implementation reads each block once: it enciphers eight blocks at a time with AES-NI, " ++
      "their tweaks computed eight at a time with PCLMULQDQ in the scratch buffer."])
    code := Impl.AesXts.X86_64AesNi.encrypt
    contract := Spec.Xts.aesEncryptContract X86_64.abi 8
    stack := 8
    verified := Proof.AesXts.X86_64.OnePassNi.encrypt_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel)
    features := ["aes", "avx", "pclmulqdq"] },
  { Spec.Xts.aesDecryptApi with
    name := Spec.Xts.aesDecryptApi.name ++ "_aesni_pclmul"
    target := X86_64.target
    doc := Spec.Xts.aesDecryptApi.doc (notes := [
      "This implementation reads each block once: it deciphers eight blocks at a time with AES-NI, " ++
      "their tweaks computed eight at a time with PCLMULQDQ in the scratch buffer."])
    code := Impl.AesXts.X86_64AesNi.decrypt
    contract := Spec.Xts.aesDecryptContract X86_64.abi 8
    stack := 8
    verified := Proof.AesXts.X86_64.OnePassNi.decrypt_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel)
    features := ["aes", "avx", "pclmulqdq"] }]

end VG.Artifacts.AesXts.X86_64
