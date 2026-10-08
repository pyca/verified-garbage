import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.AesCfb8.AArch64.Verified

/-!
# AES-CFB8 (NIST SP 800-38A §6.3, with 8-bit segments) on AArch64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_aes_encrypt_blocks` (both directions use the
forward cipher), are emitted once for each implementation
(`Variants/AesBlocks/AArch64/`), named with its suffix (e.g.
`vg_aes_cfb8_encrypt_aes`), and need its CPU features.

No stack is used: the calls keep the return address in `x30`, which each
function saves in the scratch buffer.
-/

namespace VG.Generic.AesBlocks.AArch64.AesCfb8

open VG.Proof.AesCfb8.AArch64

def artifacts (v : Proof.Aes.AArch64.BlocksImpl) : List Artifact := [
  { Spec.Cfb8.aesEncryptApi with
    name := Spec.Cfb8.aesEncryptApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.Cfb8.aesEncryptApi.doc (notes := ["This implementation enciphers one block for each byte with `" ++
      v.enc.name ++ "`."])
    code := Impl.AesCfb8.AArch64.encrypt v.enc
    contract := Spec.Cfb8.aesEncryptContract AArch64.abi
    verified := encrypt_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features },
  { Spec.Cfb8.aesDecryptApi with
    name := Spec.Cfb8.aesDecryptApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.Cfb8.aesDecryptApi.doc (notes := ["This implementation enciphers one block for each byte with `" ++
      v.enc.name ++ "`."])
    code := Impl.AesCfb8.AArch64.decrypt v.enc
    contract := Spec.Cfb8.aesDecryptContract AArch64.abi
    verified := decrypt_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features }]

end VG.Generic.AesBlocks.AArch64.AesCfb8
