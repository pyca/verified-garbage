import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.AesCcm.Arm.Frame

/-!
# AES-CCM (NIST SP 800-38C) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation.

Both functions run in a frame of 2592 bytes holding their working space
(`Proof/AesCcm/Arm/Frame.lean`). In it they call `vg_cmac_aes_update` and
`vg_aes_ctr32` in frames that push their two stack arguments, and
`vg_cmac_aes_update`'s own frame for its call of `vg_aes_ctr32` pushes two
more: 2608 bytes of stack in all.
-/

namespace VG.Artifacts.AesCcm.Arm

open VG.Proof.AesCcm.Arm

/-- Which functions `seal` and `open` call. -/
def callNote : String :=
  "This implementation computes the CBC-MAC with `vg_cmac_aes_update`, and encrypts with `vg_aes_ctr32`."

def artifacts : List Artifact := [
  { Spec.Ccm.sealApi with
    target := Arm.target
    doc := Spec.Ccm.sealApi.doc (notes := [callNote])
    code := Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesCcm.Arm.«seal»
    contract := Spec.Ccm.sealContract Arm.abi 2608
    stack := 2608
    verified := seal_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Ccm.openApi with
    target := Arm.target
    doc := Spec.Ccm.openApi.doc (notes := [callNote,
      "It compares the tags and overwrites the data with zeros without a branch on the result."])
    code := Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesCcm.Arm.«open»
    contract := Spec.Ccm.openContract Arm.abi 2608
    stack := 2608
    verified := open_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.AesCcm.Arm
