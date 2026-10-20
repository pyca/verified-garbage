module

public import VerifiedGarbage.Proof.Camellia.Arm.KeyVerified
public import VerifiedGarbage.Proof.Camellia.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Camellia.Arm

def artifacts : List Artifact := [
  Spec.Camellia.expandKeyApi.artifact Arm.target {
    notes := ["Baseline ARMv7: `KA` and `KB` by the bitsliced rounds of the block functions, on eight copies of the value; the subkeys as rotations of 32-bit words."]
    code := Impl.StackScratch.Arm.withRegScratchWiped 2720 .r3 680 Impl.Camellia.Arm.expandKey
    stack := 2720
    verified := Proof.Camellia.Arm.expandKey_framed },
  Spec.Camellia.ecbEncryptApi.artifact Arm.target {
    notes := ["Bitsliced on baseline ARMv7: 8 blocks at a time in general-purpose registers, copied through a buffer on the stack, each half as sixteen 32-bit planes, the S-boxes as Boolean circuits."]
    code := Impl.StackScratch.Arm.withStackScratchWiped 2816 0 680 (Impl.Camellia.Arm.ecb .encrypt)
    stack := 2816
    verified := Proof.Camellia.Arm.ecb_framed .encrypt },
  Spec.Camellia.ecbDecryptApi.artifact Arm.target {
    notes := ["Bitsliced on baseline ARMv7: 8 blocks at a time in general-purpose registers, copied through a buffer on the stack, each half as sixteen 32-bit planes, the S-boxes as Boolean circuits; the subkeys bitsliced in decryption's order, then encryption's rounds."]
    code := Impl.StackScratch.Arm.withStackScratchWiped 2816 0 680 (Impl.Camellia.Arm.ecb .decrypt)
    stack := 2816
    verified := Proof.Camellia.Arm.ecb_framed .decrypt }]

end VG.Artifacts.Camellia.Arm
