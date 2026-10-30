module

public import VerifiedGarbage.Proof.AesXts.X86.Verified
public import VerifiedGarbage.Proof.AesXts.X86.Unit.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) on x86

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`,
are emitted once for each implementation (`Variants/AesBlocks/X86/`), named
with its suffix (e.g. `vg_aes_xts_encrypt_aesni`), and need its CPU
features. The functions on whole data units call the whole-block functions
with the same suffix (e.g. `vg_aes_xts_encrypt_unit_aesni` calls
`vg_aes_xts_encrypt_aesni`).

The stack of the whole-block functions is 24 bytes: the five arguments of
the block function and the return address of its call. That of the
functions on whole data units is 52: the six arguments of a whole-block
function, the return address of its call, and its 24.
-/

@[expose] public section

namespace VG.Generic.AesBlocks.X86.AesXts

open VG.Proof.AesXts.X86

def artifacts (v : Proof.Aes.X86.BlocksImpl) : List Artifact := [
  Spec.Xts.aesEncryptApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesXts.X86.encrypt v.enc
    stack := 24
    verified := encrypt_verified v
    spSafe := encrypt_spSafe v
    features := v.features },
  Spec.Xts.aesDecryptApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesXts.X86.decrypt v.dec
    stack := 24
    verified := decrypt_verified v
    spSafe := decrypt_spSafe v
    features := v.features },
  Spec.Xts.aesEncryptUnitApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesXts.X86Unit.encrypt (Unit.xtsE v)
    stack := 52
    verified := Unit.encrypt_verified v
    spSafe := Unit.encrypt_spSafe v
    features := v.features },
  Spec.Xts.aesDecryptUnitApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesXts.X86Unit.decrypt (Unit.xtsE v) (Unit.xtsD v)
    stack := 52
    verified := Unit.decrypt_verified v
    spSafe := Unit.decrypt_spSafe v
    features := v.features }]

end VG.Generic.AesBlocks.X86.AesXts
