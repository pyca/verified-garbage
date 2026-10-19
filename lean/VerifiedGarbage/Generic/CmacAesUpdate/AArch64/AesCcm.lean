module

public import VerifiedGarbage.Proof.AesCcm.AArch64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch

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
save in the working space, so their code uses no stack; it reads its last
three arguments, `tag`, `tag_len` and `work`, from the stack. Each function
keeps its working space, its last argument, in a frame of 2592 bytes on the
stack that also holds a copy of `tag` and `tag_len`
(`Verified.stackArgScratch`).
-/

@[expose] public section

namespace VG.Generic.CmacAesUpdate.AArch64.AesCcm

open VG.Proof.AesCcm.AArch64

/-- Which functions an instance of `seal` or `open` calls. -/
def callNote (v : Proof.CmacAes.AArch64.UpdateImpl) : String :=
  "This implementation computes the CBC-MAC with `" ++ v.callee.name ++ "`, and encrypts with `" ++
    v.ctr.callee.name ++ "`."

def artifacts (v : Proof.CmacAes.AArch64.UpdateImpl) : List Artifact := [
  Spec.Ccm.sealApi.artifact AArch64.target {
    suffix := v.suffix
    notes := [callNote v]
    code := Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (Impl.AesCcm.AArch64.seal v.callee v.ctr.callee)
    stack := 2592
    verified := seal_framed v
    features := v.features },
  Spec.Ccm.openApi.artifact AArch64.target {
    suffix := v.suffix
    notes := [callNote v,
      "It compares the tags and overwrites the data with zeros without a branch on the result."]
    code := Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (Impl.AesCcm.AArch64.open v.callee v.ctr.callee)
    stack := 2592
    verified := open_framed v
    features := v.features }]

end VG.Generic.CmacAesUpdate.AArch64.AesCcm
