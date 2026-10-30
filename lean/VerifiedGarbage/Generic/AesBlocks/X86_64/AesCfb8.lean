module

public import VerifiedGarbage.Proof.AesCfb8.X86_64.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# AES-CFB8 (NIST SP 800-38A §6.3, with 8-bit segments) on x86-64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_aes_encrypt_blocks` (both directions use the
forward cipher), are emitted once for each implementation
(`Variants/AesBlocks/X86_64/`), named with its suffix (e.g.
`vg_aes_cfb8_encrypt_aesni`), and need its CPU features.

The stack is 8 bytes: the return address of the call of the block function,
which uses no stack.
-/

@[expose] public section

namespace VG.Generic.AesBlocks.X86_64.AesCfb8

open VG.Proof.AesCfb8.X86_64

def artifacts (v : Proof.Aes.X86_64.BlocksImpl) : List Artifact := [
  Spec.Cfb8.aesEncryptApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.AesCfb8.X86_64.encrypt v.enc
    stack := 8
    verified := encrypt_verified v
    spSafe := encrypt_spSafe v
    features := v.features },
  Spec.Cfb8.aesDecryptApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.AesCfb8.X86_64.decrypt v.enc
    stack := 8
    verified := decrypt_verified v
    spSafe := decrypt_spSafe v
    features := v.features }]

end VG.Generic.AesBlocks.X86_64.AesCfb8
