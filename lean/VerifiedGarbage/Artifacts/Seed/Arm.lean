import VerifiedGarbage.Proof.Seed.Arm.KeyVerified

/-! # SEED artifacts on baseline ARMv7 -/

namespace VG.Artifacts.Seed.Arm

def artifacts : List Artifact := [
  { Spec.Seed.expandKeyApi with
    target := Arm.target
    doc := Spec.Seed.expandKeyApi.doc
      (notes := ["Baseline ARMv7: the 32 inputs of `G` from the key words in general-purpose registers, then `G` of eight at a time, bitsliced in general-purpose registers through the AES S-box circuit (SEED's S-boxes are affine maps of AES's), with no table lookups."])
    code := Impl.StackScratch.Arm.withRegScratchWiped 752 .r2 188 Impl.Seed.Arm.expandKey
    contract := Spec.Seed.expandKeyContract Arm.abi 752
    stack := 752
    verified := Proof.Seed.Arm.expandKey_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Seed.ecbEncryptApi with
    target := Arm.target
    doc := Spec.Seed.ecbEncryptApi.doc
      (notes := ["Baseline ARMv7: eight blocks at a time, each `G` of a round bitsliced in general-purpose registers through the AES S-box circuit (SEED's S-boxes are affine maps of AES's), with no table lookups."])
    code := Impl.StackScratch.Arm.withRegScratchWiped 752 .r3 188 (Impl.Seed.Arm.ecb .encrypt)
    contract := Spec.Seed.ecbEncryptContract Arm.abi 752
    stack := 752
    ofSig := ⟨_, _, _, by unfold Spec.Seed.ecbEncryptContract Spec.Seed.ecbContract; rfl⟩
    verified := Proof.Seed.Arm.ecb_framed .encrypt
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Seed.ecbDecryptApi with
    target := Arm.target
    doc := Spec.Seed.ecbDecryptApi.doc
      (notes := ["Baseline ARMv7: eight blocks at a time, each `G` of a round bitsliced in general-purpose registers through the AES S-box circuit (SEED's S-boxes are affine maps of AES's), with no table lookups."])
    code := Impl.StackScratch.Arm.withRegScratchWiped 752 .r3 188 (Impl.Seed.Arm.ecb .decrypt)
    contract := Spec.Seed.ecbDecryptContract Arm.abi 752
    stack := 752
    ofSig := ⟨_, _, _, by unfold Spec.Seed.ecbDecryptContract Spec.Seed.ecbContract; rfl⟩
    verified := Proof.Seed.Arm.ecb_framed .decrypt
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Seed.Arm
