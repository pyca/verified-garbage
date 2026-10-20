module

public import VerifiedGarbage.Proof.AesCfb.X86.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# AES-CFB128 (NIST SP 800-38A §6.3) on x86

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_aes_encrypt_blocks` (both directions use the
forward cipher), are emitted once for each implementation
(`Variants/AesBlocks/X86/`), named with its suffix (e.g.
`vg_aes_cfb128_encrypt_aesni`), and need its CPU features.

The stack is 24 bytes: the five arguments of the block function and the
return address of its call.
-/

@[expose] public section

namespace VG.Generic.AesBlocks.X86.AesCfb

open VG.Proof.AesCfb.X86

def artifacts (v : Proof.Aes.X86.BlocksImpl) : List Artifact := [
  Spec.Cfb.aesEncryptApi.artifact X86.target {
    suffix := v.suffix
    notes := ["This implementation enciphers one block at a time with `" ++
      v.enc.name ++ "`."]
    code := Impl.AesCfb.X86.encrypt v.enc
    stack := 24
    verified := encrypt_verified v
    spSafe := encrypt_spSafe v
    features := v.features },
  Spec.Cfb.aesDecryptApi.artifact X86.target {
    suffix := v.suffix
    notes := ["This implementation enciphers one block at a time with `" ++
      v.enc.name ++ "`."]
    code := Impl.AesCfb.X86.decrypt v.enc
    stack := 24
    verified := decrypt_verified v
    spSafe := decrypt_spSafe v
    features := v.features }]

end VG.Generic.AesBlocks.X86.AesCfb
