import VerifiedGarbage.Proof.Blowfish.AArch64.KeyVerified
import VerifiedGarbage.Proof.Blowfish.AArch64.Frame

namespace VG.Artifacts.Blowfish.AArch64

def artifacts : List Artifact := [
  { Spec.Blowfish.expandKeyApi with
    target := AArch64.target
    doc := Spec.Blowfish.expandKeyApi.doc
      (notes := ["The 521 encryptions run the ECB rounds on one lane of AdvSIMD registers, with \
        the S-boxes looked up by `tbl`/`tbx` from the schedule's byte planes as it is written; \
        the initial schedule is copied from a static table. No stack."])
    consts := Impl.Blowfish.AArch64.initConsts
    code := Impl.Blowfish.AArch64.expandKey
    contract := Spec.Blowfish.expandKeyContract (AArch64.abi.withConsts Impl.Blowfish.AArch64.initConsts)
    verified := Proof.Blowfish.AArch64.expandKey_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Blowfish.ecbEncryptApi with
    target := AArch64.target
    doc := Spec.Blowfish.ecbEncryptApi.doc
      (notes := ["Sixteen blocks at a time in AdvSIMD registers, each S-box looked up by `tbl` and \
        three `tbx` per byte plane, in place in the data; the blocks left after the last sixteen \
        through the scratch buffer."])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 256 .x3 32 Impl.Blowfish.AArch64.encrypt
    contract := Spec.Blowfish.ecbEncryptContract AArch64.abi 256
    stack := 256
    ofSig := ⟨_, _, _, by unfold Spec.Blowfish.ecbEncryptContract Spec.Blowfish.ecbContract; rfl⟩
    verified := Proof.Blowfish.AArch64.ecb_framed Proof.Blowfish.AArch64.encrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Blowfish.ecbDecryptApi with
    target := AArch64.target
    doc := Spec.Blowfish.ecbDecryptApi.doc
      (notes := ["Sixteen blocks at a time in AdvSIMD registers, each S-box looked up by `tbl` and \
        three `tbx` per byte plane, in place in the data; the blocks left after the last sixteen \
        through the scratch buffer."])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 256 .x3 32 Impl.Blowfish.AArch64.decrypt
    contract := Spec.Blowfish.ecbDecryptContract AArch64.abi 256
    stack := 256
    ofSig := ⟨_, _, _, by unfold Spec.Blowfish.ecbDecryptContract Spec.Blowfish.ecbContract; rfl⟩
    verified := Proof.Blowfish.AArch64.ecb_framed Proof.Blowfish.AArch64.decrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Blowfish.AArch64
