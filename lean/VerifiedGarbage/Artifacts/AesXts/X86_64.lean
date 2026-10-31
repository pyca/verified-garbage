module

public import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Verified
public import VerifiedGarbage.Proof.AesXts.X86_64.AesNi.Verified
public import VerifiedGarbage.Proof.Framework.Registration

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

@[expose] public section

namespace VG.Artifacts.AesXts.X86_64


def artifacts : List Artifact := [
  Spec.Xts.aesEncryptApi.artifact X86_64.target {
    suffix := "_vaes_vpclmul"
    code := Impl.AesXts.X86_64Vaes.encrypt
    stack := 8
    verified := Proof.AesXts.X86_64.Vaes.encrypt_verified
    features := ["aes", "avx", "avx2", "vaes", "vpclmulqdq"] },
  Spec.Xts.aesDecryptApi.artifact X86_64.target {
    suffix := "_vaes_vpclmul"
    code := Impl.AesXts.X86_64Vaes.decrypt
    stack := 8
    verified := Proof.AesXts.X86_64.Vaes.decrypt_verified
    features := ["aes", "avx", "avx2", "vaes", "vpclmulqdq"] },
  Spec.Xts.aesEncryptApi.artifact X86_64.target {
    suffix := "_aesni_pclmul"
    code := Impl.AesXts.X86_64AesNi.encrypt
    stack := 8
    verified := Proof.AesXts.X86_64.OnePassNi.encrypt_verified
    features := ["aes", "avx", "pclmulqdq"] },
  Spec.Xts.aesDecryptApi.artifact X86_64.target {
    suffix := "_aesni_pclmul"
    code := Impl.AesXts.X86_64AesNi.decrypt
    stack := 8
    verified := Proof.AesXts.X86_64.OnePassNi.decrypt_verified
    features := ["aes", "avx", "pclmulqdq"] }]

end VG.Artifacts.AesXts.X86_64
