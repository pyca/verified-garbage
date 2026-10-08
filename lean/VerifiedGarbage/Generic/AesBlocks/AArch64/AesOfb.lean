import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.AesOfb.AArch64.Verified

/-!
# AES-OFB (NIST SP 800-38A §6.4) on AArch64

A generic file (see `TCB/Emit.lean`): the artifact it lists, calling an
implementation `v` of `vg_aes_encrypt_blocks`, is emitted once for each
implementation (`Variants/AesBlocks/AArch64/`), named with its suffix (e.g.
`vg_aes_ofb_aes`), and needs its CPU features.

No stack is used: the calls keep the return address in `x30`, which the
function saves in the scratch buffer.
-/

namespace VG.Generic.AesBlocks.AArch64.AesOfb

open VG.Proof.AesOfb.AArch64

def artifacts (v : Proof.Aes.AArch64.BlocksImpl) : List Artifact := [
  { Spec.Ofb.aesApi with
    name := Spec.Ofb.aesApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.Ofb.aesApi.doc (notes := ["This implementation enciphers one block at a time with `" ++
      v.enc.name ++ "`."])
    code := Impl.AesOfb.AArch64.crypt v.enc
    contract := Spec.Ofb.aesContract AArch64.abi
    verified := crypt_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features }]

end VG.Generic.AesBlocks.AArch64.AesOfb
