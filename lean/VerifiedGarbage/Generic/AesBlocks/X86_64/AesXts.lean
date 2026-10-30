module

public import VerifiedGarbage.Proof.AesXts.X86_64.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.AesXts.X86_64.Body

/-!
# XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) on x86-64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`,
are emitted once for each implementation (`Variants/AesBlocks/X86_64/`),
named with its suffix (e.g. `vg_aes_xts_encrypt_aesni`), and need its CPU
features.

The stack is 8 bytes: the return address of the call of the block function,
which uses no stack.
-/

@[expose] public section

namespace VG.Generic.AesBlocks.X86_64.AesXts

open VG.Proof.AesXts.X86_64

def artifacts (v : Proof.Aes.X86_64.BlocksImpl) : List Artifact := [
  Spec.Xts.aesEncryptApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.AesXts.X86_64.encrypt v.enc
    stack := 8
    verified := encrypt_verified v
    spSafe := encrypt_spSafe v
    features := v.features },
  Spec.Xts.aesDecryptApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.AesXts.X86_64.decrypt v.dec
    stack := 8
    verified := decrypt_verified v
    spSafe := decrypt_spSafe v
    features := v.features }]

end VG.Generic.AesBlocks.X86_64.AesXts
