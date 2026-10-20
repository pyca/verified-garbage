module

public import VerifiedGarbage.Proof.AesCbc.AArch64.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# AES-CBC (NIST SP 800-38A §6.2) on AArch64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`,
are emitted once for each implementation (`Variants/AesBlocks/AArch64/`),
named with its suffix (e.g. `vg_aes_cbc_encrypt_aes`), and need its CPU
features.

No stack is used: the calls keep the return address in `x30`, which each
function saves in the scratch buffer.
-/

@[expose] public section

namespace VG.Generic.AesBlocks.AArch64.AesCbc

open VG.Proof.AesCbc.AArch64

def artifacts (v : Proof.Aes.AArch64.BlocksImpl) : List Artifact := [
  Spec.Cbc.aesEncryptApi.artifact AArch64.target {
    suffix := v.suffix
    notes := ["This implementation enciphers one block at a time with `" ++
      v.enc.name ++ "`."]
    code := Impl.AesCbc.AArch64.encrypt v.enc
    verified := encrypt_verified v
    features := v.features },
  Spec.Cbc.aesDecryptApi.artifact AArch64.target {
    suffix := v.suffix
    notes := ["This implementation deciphers one block at a time with `" ++
      v.dec.name ++ "`."]
    code := Impl.AesCbc.AArch64.decrypt v.dec
    verified := decrypt_verified v
    features := v.features }]

end VG.Generic.AesBlocks.AArch64.AesCbc
