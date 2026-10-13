module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Verified

/-!
# XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) on x86-64, in one pass

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. They are the variants `_vaes_vpclmul` of `vg_aes_xts_encrypt` and
`vg_aes_xts_decrypt` (whose instances for each implementation of the block
functions are in `Generic/AesBlocks/X86_64/AesXts.lean`): they call nothing,
and keep the tweaks of eight blocks in registers, computing the next eight
with VPCLMULQDQ.

They write no stack; the 8 bytes are those of the shared precondition.
-/

@[expose] public section

namespace VG.Artifacts.AesXts.X86_64

open VG.Proof.AesXts.X86_64.Vaes

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
    verified := encrypt_verified
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
    verified := decrypt_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel)
    features := ["aes", "avx", "avx2", "vaes", "vpclmulqdq"] }]

end VG.Artifacts.AesXts.X86_64
