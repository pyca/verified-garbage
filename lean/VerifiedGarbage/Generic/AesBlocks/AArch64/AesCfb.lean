module

public import VerifiedGarbage.Proof.AesCfb.AArch64.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.AesCfb.AArch64.Body

/-!
# AES-CFB128 (NIST SP 800-38A §6.3) on AArch64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_aes_encrypt_blocks` (both directions use the
forward cipher), are emitted once for each implementation
(`Variants/AesBlocks/AArch64/`), named with its suffix (e.g.
`vg_aes_cfb128_encrypt_aes`), and need its CPU features.

No stack is used: the calls keep the return address in `x30`, which each
function saves in the scratch buffer.
-/

@[expose] public section

namespace VG.Generic.AesBlocks.AArch64.AesCfb

open VG.Proof.AesCfb.AArch64

def artifacts (v : Proof.Aes.AArch64.BlocksImpl) : List Artifact := [
  Spec.Cfb.aesEncryptApi.artifact AArch64.target {
    suffix := v.suffix
    notes := ["This implementation enciphers one block at a time with `" ++
      v.enc.name ++ "`."]
    code := Impl.AesCfb.AArch64.encrypt v.enc
    verified := encrypt_verified v
    features := v.features },
  Spec.Cfb.aesDecryptApi.artifact AArch64.target {
    suffix := v.suffix
    notes := ["This implementation enciphers one block at a time with `" ++
      v.enc.name ++ "`."]
    code := Impl.AesCfb.AArch64.decrypt v.enc
    verified := decrypt_verified v
    features := v.features }]

end VG.Generic.AesBlocks.AArch64.AesCfb
