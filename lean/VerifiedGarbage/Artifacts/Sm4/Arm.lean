module

public import VerifiedGarbage.Proof.Sm4.Arm.KeyVerified
public import VerifiedGarbage.Proof.Sm4.Arm.EcbCall
import Mathlib.Tactic.SplitIfs

/-! # SM4 artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sm4.Arm

def artifacts : List Artifact := [
  { Spec.Sm4.expandKeyApi with
    target := Arm.target
    doc := Spec.Sm4.expandKeyApi.doc
      (notes := ["Baseline ARMv7: the key schedule's rounds bitsliced in general-purpose registers, eight copies of the key at a time, through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups."])
    code := Impl.StackScratch.Arm.withRegScratchWiped 1456 .r2 364 Impl.Sm4.Arm.expandKey
    contract := Spec.Sm4.expandKeyContract Arm.abi 1456
    stack := 1456
    verified := Proof.Sm4.Arm.expandKey_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sm4.ecbDirApi with
    target := Arm.target
    doc := Spec.Sm4.ecbDirApi.doc
      (notes := ["Baseline ARMv7: eight blocks at a time, bitsliced in general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups; `decrypt` selects the order in which the round keys are copied into the working space, and the rounds are the same."])
    code := Impl.Sm4.Arm.ecbAnyCode
    contract := Spec.Sm4.ecbDirContract Arm.abi 1472
    stack := 1472
    verified := Proof.Sm4.Arm.ecbAny_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sm4.ecbEncryptApi with
    target := Arm.target
    doc := Spec.Sm4.ecbEncryptApi.doc
      (notes := ["Baseline ARMv7: calls `vg_sm4_ecb` with `decrypt = 0`."])
    code := Impl.Sm4.Arm.ecbCall .encrypt
    contract := Spec.Sm4.ecbEncryptContract Arm.abi 1480
    stack := 1480
    ofSig := by exact (⟨_, _, _, by unfold Spec.Sm4.ecbEncryptContract Spec.Sm4.ecbContract; rfl⟩)
    verified := Proof.Sm4.Arm.ecbCall_verified .encrypt
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sm4.ecbDecryptApi with
    target := Arm.target
    doc := Spec.Sm4.ecbDecryptApi.doc
      (notes := ["Baseline ARMv7: calls `vg_sm4_ecb` with `decrypt = 1`."])
    code := Impl.Sm4.Arm.ecbCall .decrypt
    contract := Spec.Sm4.ecbDecryptContract Arm.abi 1480
    stack := 1480
    ofSig := by exact (⟨_, _, _, by unfold Spec.Sm4.ecbDecryptContract Spec.Sm4.ecbContract; rfl⟩)
    verified := Proof.Sm4.Arm.ecbCall_verified .decrypt
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Sm4.Arm
