module

public import VerifiedGarbage.Proof.AesCtr.AArch64.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# AES-CTR (NIST SP 800-38A §6.5) on AArch64

A generic file (see `TCB/Emit.lean`): the artifact it lists, calling an
implementation `v` of `vg_aes_ctr32`, is emitted once for each
implementation (`Variants/AesCtr32/AArch64/`), named with its suffix (e.g.
`vg_aes_ctr_aes`), and needs its CPU features.

No stack is used: the calls keep the return address in `x30`, which the
function saves in the scratch buffer.
-/

@[expose] public section

namespace VG.Generic.AesCtr32.AArch64.AesCtr

open VG.Proof.AesCtr.AArch64

def artifacts (v : Proof.Aes.AArch64.Ctr32Impl) : List Artifact := [
  Spec.Ctr.aesApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.AesCtr.AArch64.crypt v.callee
    verified := crypt_verified v
    features := v.features }]

end VG.Generic.AesCtr32.AArch64.AesCtr
