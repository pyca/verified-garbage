module

public import VerifiedGarbage.Proof.AesCtr.X86.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# AES-CTR (NIST SP 800-38A §6.5) on x86

A generic file (see `TCB/Emit.lean`): the artifact it lists, calling an
implementation `v` of `vg_aes_encrypt_blocks`, is emitted once for each
implementation (`Variants/AesBlocks/X86/`), named with its suffix (e.g.
`vg_aes_ctr_aesni`), and needs its CPU features.

The stack is 24 bytes: the five arguments of the block function and the
return address of its call.
-/

@[expose] public section

namespace VG.Generic.AesBlocks.X86.AesCtr

open VG.Proof.AesCtr.X86

def artifacts (v : Proof.Aes.X86.BlocksImpl) : List Artifact := [
  Spec.Ctr.aesApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesCtr.X86.crypt v.enc
    stack := 24
    verified := crypt_verified v
    spSafe := crypt_spSafe v
    features := v.features }]

end VG.Generic.AesBlocks.X86.AesCtr
