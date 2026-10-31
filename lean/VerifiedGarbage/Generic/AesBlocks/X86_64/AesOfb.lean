module

public import VerifiedGarbage.Proof.AesOfb.X86_64.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# AES-OFB (NIST SP 800-38A §6.4) on x86-64

A generic file (see `TCB/Emit.lean`): the artifact it lists, calling an
implementation `v` of `vg_aes_encrypt_blocks`, is emitted once for each
implementation (`Variants/AesBlocks/X86_64/`), named with its suffix (e.g.
`vg_aes_ofb_aesni`), and needs its CPU features.

The stack is 8 bytes: the return address of the call of the block function,
which uses no stack.
-/

@[expose] public section

namespace VG.Generic.AesBlocks.X86_64.AesOfb

open VG.Proof.AesOfb.X86_64

def artifacts (v : Proof.Aes.X86_64.BlocksImpl) : List Artifact := [
  Spec.Ofb.aesApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.AesOfb.X86_64.crypt v.enc
    stack := 8
    verified := crypt_verified v
    spSafe := crypt_spSafe v
    features := v.features }]

end VG.Generic.AesBlocks.X86_64.AesOfb
