module

public import VerifiedGarbage.Proof.Sm4.Arm.PreparedVerified
public import VerifiedGarbage.Proof.Sm4.Arm.KeyVerified
public import VerifiedGarbage.Proof.Sm4.Arm.EcbCall
public import VerifiedGarbage.Proof.Sm4.Arm.EcbAny
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SM4 artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sm4.Arm

def artifacts : List Artifact := [
  Spec.Sm4.expandKeyApi.artifact Arm.target {
    notes := ["Baseline ARMv7: the key schedule's rounds bitsliced in general-purpose registers, eight copies of the key at a time, through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups."]
    code := Impl.StackScratch.Arm.withRegScratchWiped 1456 .r2 364 Impl.Sm4.Arm.expandKey
    stack := 1456
    verified := Proof.Sm4.Arm.expandKey_framed },
  Spec.Sm4.ecbDirApi.artifact Arm.target {
    notes := ["Baseline ARMv7: eight blocks at a time, bitsliced in general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups; `decrypt` selects the order in which the round keys are copied into the working space, and the rounds are the same."]
    code := Impl.Sm4.Arm.ecbAnyCode
    stack := 1472
    verified := Proof.Sm4.Arm.ecbAny_framed },
  Spec.Sm4.ecbEncryptApi.artifact Arm.target {
    notes := ["Baseline ARMv7: calls `vg_sm4_ecb` with `decrypt = 0`."]
    code := Impl.Sm4.Arm.ecbCall .encrypt
    stack := 1480
    verified := Proof.Sm4.Arm.ecbCall_verified .encrypt },
  Spec.Sm4.ecbDecryptApi.artifact Arm.target {
    notes := ["Baseline ARMv7: calls `vg_sm4_ecb` with `decrypt = 1`."]
    code := Impl.Sm4.Arm.ecbCall .decrypt
    stack := 1480
    verified := Proof.Sm4.Arm.ecbCall_verified .decrypt },
  (Spec.Sm4.Prepared.prepareApi Impl.Sm4.Arm.layout).artifact Arm.target {
    notes := ["Baseline ARMv7: bitslices the round keys once into ECB's working space, in the selected direction, with no table lookups."]
    code := Impl.Sm4.Arm.prepareKeys
    stack := 0
    verified := Proof.Sm4.Arm.prepare_verified },
  (Spec.Sm4.Prepared.cryptApi Impl.Sm4.Arm.layout).artifact Arm.target {
    notes := ["Baseline ARMv7: ECB's eight-block bitsliced core under the prepared round keys, which it preserves for further batches, with no table lookups."]
    code := Impl.Sm4.Arm.cryptPrepared
    stack := 0
    verified := Proof.Sm4.Arm.crypt_verified }]

end VG.Artifacts.Sm4.Arm
