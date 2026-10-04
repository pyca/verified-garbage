import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.AesGcmSiv.Arm.Verified

/-!
# AES-GCM-SIV (RFC 8452) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation.

Both functions call `vg_aes_ctr32` and `vg_ghash` in frames that push their
two stack arguments, so use 8 bytes of stack (`vg_aes_expand_key` takes no
stack arguments).
-/

namespace VG.Artifacts.AesGcmSiv.Arm

open VG.Proof.AesGcmSiv.Arm

/-- Which functions the implementation calls. -/
def note : String := "This implementation encrypts with `vg_aes_ctr32` (and expands keys with \
  `vg_aes_expand_key`) and computes POLYVAL with `vg_ghash`."

def artifacts : List Artifact := [
  { Spec.GcmSiv.sealApi with
    target := Arm.target
    doc := Spec.GcmSiv.sealApi.doc (notes := [note])
    code := Impl.AesGcmSiv.Arm.«seal»
    contract := Spec.GcmSiv.sealContract Arm.abi 8
    stack := 8
    verified := seal_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.GcmSiv.openApi with
    target := Arm.target
    doc := Spec.GcmSiv.openApi.doc (notes := [note,
      "It compares the tags and overwrites the data with zeros without a branch on the result."])
    code := Impl.AesGcmSiv.Arm.«open»
    contract := Spec.GcmSiv.openContract Arm.abi 8
    stack := 8
    verified := open_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.AesGcmSiv.Arm
