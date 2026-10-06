import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.AesSiv.AArch64.Frame

/-!
# AES-SIV (RFC 5297) key setup on AArch64

A generic file (see `TCB/Emit.lean`): `vg_aes_siv_init`, calling an
implementation `v` of `vg_aes_ctr32` (through the CMAC subkeys made with it)
and the implementation of `vg_aes_expand_key_scratch` that goes with it, is emitted
once for each implementation (`Variants/AesCtr32/AArch64/`), named with its
suffix (e.g. `vg_aes_siv_init_aes`), and needs its CPU features.
`vg_aes_siv_encrypt` and `vg_aes_siv_decrypt`, which also call
`vg_cmac_aes_update`, follow its implementations instead
(`Generic/CmacAesUpdate/AArch64/AesSiv.lean`).

`init` keeps its working space in a frame of its own
(`Proof/AesSiv/AArch64/Frame.lean`): its `stack` is that frame. Its calls
(`bl`) keep the return address in `x30`, which it saves in the working space.
-/

namespace VG.Generic.AesCtr32.AArch64.AesSiv

open VG.Proof.AesSiv.AArch64

def artifacts (v : Proof.Aes.AArch64.Ctr32Impl) : List Artifact := [
  { Spec.Siv.initApi with
    name := Spec.Siv.initApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.Siv.initApi.doc (notes := [
      "This implementation expands the keys with `" ++ v.expand.name ++ "` and computes the CMAC subkeys \
      with `" ++ Spec.Cmac.aesSubkeysApi.name ++ v.suffix ++ "`."])
    code := Impl.StackScratch.AArch64.withStackScratch 2560 .x3
      (Impl.AesSiv.AArch64.init v.expand v.callee v.suffix)
    contract := Spec.Siv.initContract AArch64.abi 2560
    stack := 2560
    verified := init_framed v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features }]

end VG.Generic.AesCtr32.AArch64.AesSiv
