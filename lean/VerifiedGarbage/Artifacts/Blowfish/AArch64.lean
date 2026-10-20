module

public import VerifiedGarbage.Proof.Blowfish.AArch64.KeyVerified
public import VerifiedGarbage.Proof.Blowfish.AArch64.Frame
public import VerifiedGarbage.Proof.Blowfish.AArch64.Verified
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Blowfish.AArch64

def artifacts : List Artifact := [
  Spec.Blowfish.expandKeyApi.artifact AArch64.target {
    notes := ["The 521 encryptions run the ECB rounds on one lane of AdvSIMD registers, with \
        the S-boxes looked up by `tbl`/`tbx` from the schedule's byte planes as it is written; \
        the initial schedule is copied from a static table. No stack."]
    consts := Impl.Blowfish.AArch64.initConsts
    code := Impl.Blowfish.AArch64.expandKey
    verified := Proof.Blowfish.AArch64.expandKey_verified },
  Spec.Blowfish.ecbEncryptApi.artifact AArch64.target {
    notes := ["Sixteen blocks at a time in AdvSIMD registers, each S-box looked up by `tbl` and \
        three `tbx` per byte plane, in place in the data; the blocks left after the last sixteen \
        through the scratch buffer."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 256 .x3 32 Impl.Blowfish.AArch64.encrypt
    stack := 256
    verified := Proof.Blowfish.AArch64.ecb_framed Proof.Blowfish.AArch64.encrypt_verified },
  Spec.Blowfish.ecbDecryptApi.artifact AArch64.target {
    notes := ["Sixteen blocks at a time in AdvSIMD registers, each S-box looked up by `tbl` and \
        three `tbx` per byte plane, in place in the data; the blocks left after the last sixteen \
        through the scratch buffer."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 256 .x3 32 Impl.Blowfish.AArch64.decrypt
    stack := 256
    verified := Proof.Blowfish.AArch64.ecb_framed Proof.Blowfish.AArch64.decrypt_verified }]

end VG.Artifacts.Blowfish.AArch64
