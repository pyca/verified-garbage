import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.AesXts.AArch64.Verified

/-!
# XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) on AArch64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`,
are emitted once for each implementation (`Variants/AesBlocks/AArch64/`),
named with its suffix (e.g. `vg_aes_xts_encrypt_aes`), and need its CPU
features.

No stack is used: the calls keep the return address in `x30`, which each
function saves in the scratch buffer.
-/

namespace VG.Generic.AesBlocks.AArch64.AesXts

open VG.Proof.AesXts.AArch64

def artifacts (v : Proof.Aes.AArch64.BlocksImpl) : List Artifact := [
  { Spec.Xts.aesEncryptApi with
    name := Spec.Xts.aesEncryptApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.Xts.aesEncryptApi.doc (notes := ["This implementation enciphers one block at a time with `" ++
      v.enc.name ++ "`."])
    code := Impl.AesXts.AArch64.encrypt v.enc
    contract := Spec.Xts.aesEncryptContract AArch64.abi
    verified := encrypt_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features },
  { Spec.Xts.aesDecryptApi with
    name := Spec.Xts.aesDecryptApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.Xts.aesDecryptApi.doc (notes := ["This implementation deciphers one block at a time with `" ++
      v.dec.name ++ "`."])
    code := Impl.AesXts.AArch64.decrypt v.dec
    contract := Spec.Xts.aesDecryptContract AArch64.abi
    verified := decrypt_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features }]

end VG.Generic.AesBlocks.AArch64.AesXts
