import VerifiedGarbage.Proof.Sm4.Arm.KeyVerified

/-! # SM4 artifacts on baseline ARMv7 -/

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
  { Spec.Sm4.ecbEncryptApi with
    target := Arm.target
    doc := Spec.Sm4.ecbEncryptApi.doc
      (notes := ["Baseline ARMv7: eight blocks at a time, bitsliced in general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups."])
    code := Impl.StackScratch.Arm.withRegScratchWiped 1456 .r3 364 (Impl.Sm4.Arm.ecb .encrypt)
    contract := Spec.Sm4.ecbEncryptContract Arm.abi 1456
    stack := 1456
    ofSig := ⟨_, _, _, by unfold Spec.Sm4.ecbEncryptContract Spec.Sm4.ecbContract; rfl⟩
    verified := Proof.Sm4.Arm.ecb_framed .encrypt
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sm4.ecbDecryptApi with
    target := Arm.target
    doc := Spec.Sm4.ecbDecryptApi.doc
      (notes := ["Baseline ARMv7: eight blocks at a time, bitsliced in general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups."])
    code := Impl.StackScratch.Arm.withRegScratchWiped 1456 .r3 364 (Impl.Sm4.Arm.ecb .decrypt)
    contract := Spec.Sm4.ecbDecryptContract Arm.abi 1456
    stack := 1456
    ofSig := ⟨_, _, _, by unfold Spec.Sm4.ecbDecryptContract Spec.Sm4.ecbContract; rfl⟩
    verified := Proof.Sm4.Arm.ecb_framed .decrypt
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Sm4.Arm
