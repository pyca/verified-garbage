module

public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Aes.Arm.Ctr32
import VerifiedGarbage.Proof.Aes.Arm.ExpandKey
public import VerifiedGarbage.Proof.Aes.Arm.Blocks
public import VerifiedGarbage.Proof.Aes.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Aes.Arm

def artifacts : List Artifact := [
  Spec.Aes.expandKeyApi.artifact Arm.target {
    notes := ["`SUBWORD` uses a constant-time bitsliced S-box, in the style of BearSSL's \
        `aes_ct` (Thomas Pornin, MIT licence). The working space is in a frame of 512 bytes \
        on the stack, zeroed before returning."]
    code := Impl.StackScratch.Arm.withRegScratchWiped 512 .r3 128 Impl.Aes.Arm.expandKey
    stack := 512
    verified := Proof.Aes.Arm.expandKey_framed },
  Spec.Aes.expandKeyScratchApi.artifact Arm.target {
    notes := ["`SUBWORD` uses a constant-time bitsliced S-box, in the style of BearSSL's \
        `aes_ct` (Thomas Pornin, MIT licence)."]
    code := Impl.Aes.Arm.expandKey
    verified := Proof.Aes.Arm.expandKey_verified },
  Spec.Gcm.ctr32Api.artifact Arm.target {
    notes := ["Constant-time bitsliced AES, two blocks at a time, in the style of BearSSL's \
        `aes_ct` (Thomas Pornin, MIT licence)."]
    code := Impl.Aes.Arm.ctr32
    verified := Proof.Aes.Arm.ctr32_verified },
  Spec.Aes.encryptBlocksApi.artifact Arm.target {
    notes := ["Constant-time bitsliced AES, two blocks at a time, in the style of BearSSL's \
        `aes_ct` (Thomas Pornin, MIT licence)."]
    code := Impl.Aes.Arm.encryptBlocks
    verified := Proof.Aes.Arm.Ecb.encryptBlocks_verified },
  Spec.Aes.decryptBlocksApi.artifact Arm.target {
    notes := ["Constant-time bitsliced AES, two blocks at a time, in the style of BearSSL's \
        `aes_ct` (Thomas Pornin, MIT licence): the inverse S-box is the forward one between \
        two inverse affine maps."]
    code := Impl.Aes.Arm.decryptBlocks
    verified := Proof.Aes.Arm.Ecb.decryptBlocks_verified }]

end VG.Artifacts.Aes.Arm
