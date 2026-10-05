import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.AesSiv.AArch64.Frame

/-!
# AES-SIV (RFC 5297) encryption and decryption on AArch64

A generic file (see `TCB/Emit.lean`): `vg_aes_siv_encrypt` and
`vg_aes_siv_decrypt`, calling an implementation `v` of `vg_cmac_aes_update`,
and the CMAC functions and `vg_aes_ctr32` made with the implementation of
AES that goes with it (`v.ctr`), are emitted once for each implementation
of the update (`Variants/CmacAesUpdate/AArch64/`), named with its suffix
(e.g. `vg_aes_siv_encrypt_aes_cbc`), and need its CPU features.

Each function keeps its working space, 2576 bytes, in a frame of its own
(`Proof/AesSiv/AArch64/Frame.lean`): its `stack` is that frame. Their calls
(`bl`) keep the return address in `x30`, which they save in the working
space.
-/

namespace VG.Generic.CmacAesUpdate.AArch64.AesSiv

open VG.Proof.AesSiv.AArch64

/-- Which functions an instance of `encrypt` or `decrypt` calls. -/
def cryptNote (v : Proof.CmacAes.AArch64.UpdateImpl) : String :=
  "This implementation chains the blocks of CMAC with `" ++ v.callee.name ++ "`, calls the other CMAC \
    functions made with `" ++ v.ctr.callee.name ++ "` (e.g. `" ++ Spec.Cmac.aesFinalizeApi.name ++
    v.ctr.suffix ++ "`), and encrypts with `" ++ v.ctr.callee.name ++ "`."

def artifacts (v : Proof.CmacAes.AArch64.UpdateImpl) : List Artifact := [
  { Spec.Siv.encryptApi with
    name := Spec.Siv.encryptApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.Siv.encryptApi.doc (notes := [cryptNote v])
    code := Impl.StackScratch.AArch64.withStackScratch 2576 .x7
      (Impl.AesSiv.AArch64.encrypt v.callee v.ctr.callee v.ctr.suffix)
    contract := Spec.Siv.encryptContract AArch64.abi 2576
    stack := 2576
    verified := encrypt_framed v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features },
  { Spec.Siv.decryptApi with
    name := Spec.Siv.decryptApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.Siv.decryptApi.doc (notes := [cryptNote v,
      "It compares the IVs and overwrites the data with zeros without a branch on the result."])
    code := Impl.StackScratch.AArch64.withStackScratch 2576 .x7
      (Impl.AesSiv.AArch64.decrypt v.callee v.ctr.callee v.ctr.suffix)
    contract := Spec.Siv.decryptContract AArch64.abi 2576
    stack := 2576
    verified := decrypt_framed v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features }]

end VG.Generic.CmacAesUpdate.AArch64.AesSiv
