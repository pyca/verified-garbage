import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.AesCcm.AArch64.Verified

/-!
# AES-CCM (NIST SP 800-38C) on AArch64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_cmac_aes_update` for the CBC-MAC, and the
implementation of `vg_aes_ctr32` that goes with it (`v.ctr`) for counter
mode, are emitted once for each implementation
(`Variants/CmacAesUpdate/AArch64/`), named with its suffix (e.g.
`vg_aes_ccm_seal_aes_cbc`), and need its CPU features.
**Review note**: `sig` and `doc` are trusted, as they tie the Rust caller to
the contract; these artifacts are made from each function's `Api` (in
`Spec/`, reviewed with the contract), and this file adds only notes on the
implementation.

The functions' calls (`bl`) keep the return address in `x30`, which they
save in the working space, so they use no stack; they read their last two
arguments, `work` and `tag_len`, from the stack.
-/

namespace VG.Generic.CmacAesUpdate.AArch64.AesCcm

open VG.Proof.AesCcm.AArch64

/-- Which functions an instance of `seal` or `open` calls. -/
def callNote (v : Proof.CmacAes.AArch64.UpdateImpl) : String :=
  "This implementation computes the CBC-MAC with `" ++ v.callee.name ++ "`, and encrypts with `" ++
    v.ctr.callee.name ++ "`."

def artifacts (v : Proof.CmacAes.AArch64.UpdateImpl) : List Artifact := [
  { Spec.Ccm.sealApi with
    name := Spec.Ccm.sealApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.Ccm.sealApi.doc (notes := [callNote v])
    code := Impl.AesCcm.AArch64.seal v.callee v.ctr.callee
    contract := Spec.Ccm.sealContract AArch64.abi
    verified := seal_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features },
  { Spec.Ccm.openApi with
    name := Spec.Ccm.openApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.Ccm.openApi.doc (notes := [callNote v,
      "It compares the tags and overwrites the data with zeros without a branch on the result."])
    code := Impl.AesCcm.AArch64.open v.callee v.ctr.callee
    contract := Spec.Ccm.openContract AArch64.abi
    verified := open_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features }]

end VG.Generic.CmacAesUpdate.AArch64.AesCcm
