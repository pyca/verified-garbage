import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.AesOcb.Arm.Init
import VerifiedGarbage.Proof.AesOcb.Arm.Frame

/-!
# AES-OCB (RFC 7253) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation.

An AES-OCB key context is an AES-GCM one (the key schedule, then the
encrypted zero block at byte 240), so `init` is AES-GCM's code, in a frame of
2560 bytes holding its working space (`Proof/AesOcb/Arm/Init.lean`). `seal`
and `open` run in a frame of 2592 bytes holding theirs
(`Proof/AesOcb/Arm/Frame.lean`), and call `vg_aes_encrypt_blocks` and
`vg_aes_decrypt_blocks` in frames that push their stack argument and `lr`:
2600 bytes of stack in all.
-/

namespace VG.Artifacts.AesOcb.Arm

open VG.Proof.AesOcb.Arm

/-- How `init` is built. -/
def initNote : String := "This implementation calls `vg_aes_expand_key` for the key schedule and \
  `vg_aes_ctr32` to encrypt the zero block into `L_*`."

def artifacts : List Artifact := [
  { Spec.Ocb.initApi with
    target := Arm.target
    doc := Spec.Ocb.initApi.doc (notes := [initNote])
    code := Impl.StackScratch.Arm.withRegScratch 2560 .r3 Impl.AesGcm.Arm.init
    contract := Spec.Ocb.initContract Arm.abi 2568
    stack := 2568
    verified := init_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Ocb.sealApi with
    target := Arm.target
    doc := Spec.Ocb.sealApi.doc (notes := ["This implementation enciphers with `vg_aes_encrypt_blocks`."])
    code := Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesOcb.Arm.«seal»
    contract := Spec.Ocb.sealContract Arm.abi 2600
    stack := 2600
    verified := seal_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Ocb.openApi with
    target := Arm.target
    doc := Spec.Ocb.openApi.doc (notes := [
      "This implementation enciphers with `vg_aes_encrypt_blocks`, and deciphers with `vg_aes_decrypt_blocks`.",
      "It compares the tags and overwrites the data with zeros without a branch on the result."])
    code := Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesOcb.Arm.«open»
    contract := Spec.Ocb.openContract Arm.abi 2600
    stack := 2600
    verified := open_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.AesOcb.Arm
