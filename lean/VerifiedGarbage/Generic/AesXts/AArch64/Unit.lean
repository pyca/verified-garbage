module

public import VerifiedGarbage.Proof.AesXts.AArch64.Unit.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) of whole data units on AArch64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_aes_xts_encrypt` and `vg_aes_xts_decrypt`, are
emitted once for each implementation (`Variants/AesXts/AArch64/`), named
with its suffix (e.g. `vg_aes_xts_encrypt_unit_aes`), and need its CPU
features.

No stack is used: the calls keep the return address in `x30`, which each
function saves in the scratch buffer.
-/

@[expose] public section

namespace VG.Generic.AesXts.AArch64.Unit

open VG.Proof.AesXts.AArch64.Unit

def artifacts (v : Proof.AesXts.AArch64.XtsImpl) : List Artifact := [
  Spec.Xts.aesEncryptUnitApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.AesXts.AArch64Unit.encrypt v.enc
    verified := encrypt_verified v
    features := v.features },
  Spec.Xts.aesDecryptUnitApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.AesXts.AArch64Unit.decrypt v.enc v.dec
    verified := decrypt_verified v
    features := v.features }]

end VG.Generic.AesXts.AArch64.Unit
