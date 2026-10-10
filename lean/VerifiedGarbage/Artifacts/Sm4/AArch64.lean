import VerifiedGarbage.Proof.Sm4.AArch64.KeyVerified

/-! # SM4 artifacts on baseline AArch64 -/

namespace VG.Artifacts.Sm4.AArch64

def artifacts : List Artifact := [
  { Spec.Sm4.expandKeyApi with
    target := AArch64.target
    doc := Spec.Sm4.expandKeyApi.doc
      (notes := ["Baseline AArch64: the key schedule's rounds bitsliced in general-purpose registers, sixteen copies of the key at a time, through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups."])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3152 .x2 394 Impl.Sm4.AArch64.expandKey
    contract := Spec.Sm4.expandKeyContract AArch64.abi 3152
    stack := 3152
    verified := Proof.Sm4.AArch64.expandKey_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sm4.ecbEncryptApi with
    target := AArch64.target
    doc := Spec.Sm4.ecbEncryptApi.doc
      (notes := ["Baseline AArch64: sixteen blocks at a time, bitsliced in general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups."])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3152 .x3 394 (Impl.Sm4.AArch64.ecb .encrypt)
    contract := Spec.Sm4.ecbEncryptContract AArch64.abi 3152
    stack := 3152
    ofSig := ⟨_, _, _, by unfold Spec.Sm4.ecbEncryptContract Spec.Sm4.ecbContract; rfl⟩
    verified := Proof.Sm4.AArch64.ecb_framed .encrypt
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sm4.ecbDecryptApi with
    target := AArch64.target
    doc := Spec.Sm4.ecbDecryptApi.doc
      (notes := ["Baseline AArch64: sixteen blocks at a time, bitsliced in general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups."])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3152 .x3 394 (Impl.Sm4.AArch64.ecb .decrypt)
    contract := Spec.Sm4.ecbDecryptContract AArch64.abi 3152
    stack := 3152
    ofSig := ⟨_, _, _, by unfold Spec.Sm4.ecbDecryptContract Spec.Sm4.ecbContract; rfl⟩
    verified := Proof.Sm4.AArch64.ecb_framed .decrypt
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Sm4.AArch64
