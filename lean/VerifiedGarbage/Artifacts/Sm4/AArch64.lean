module

public import VerifiedGarbage.Proof.Sm4.AArch64.KeyVerified
public import VerifiedGarbage.Proof.Sm4.AArch64.EcbCall
import Mathlib.Tactic.SplitIfs

/-! # SM4 artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sm4.AArch64

def artifacts : List Artifact := [
  { Spec.Sm4.expandKeyApi with
    target := AArch64.target
    doc := Spec.Sm4.expandKeyApi.doc
      (notes := ["Baseline AArch64: the key schedule's rounds bitsliced in general-purpose registers, sixteen copies of the key at a time, through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups."])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3168 .x2 396 Impl.Sm4.AArch64.expandKey
    contract := Spec.Sm4.expandKeyContract AArch64.abi 3168
    stack := 3168
    verified := Proof.Sm4.AArch64.expandKey_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sm4.ecbDirApi with
    target := AArch64.target
    doc := Spec.Sm4.ecbDirApi.doc
      (notes := ["Baseline AArch64: sixteen blocks at a time, bitsliced in general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups; `decrypt` selects the order in which the round keys are bitsliced into the working space, and the rounds are the same."])
    code := Proof.Sm4.AArch64.ecbAnyFramed
    contract := Spec.Sm4.ecbDirContract AArch64.abi 3168
    stack := 3168
    verified := Proof.Sm4.AArch64.ecbAny_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sm4.ecbEncryptApi with
    target := AArch64.target
    doc := Spec.Sm4.ecbEncryptApi.doc
      (notes := ["Baseline AArch64: calls `vg_sm4_ecb` with `decrypt = 0`, saving the link register in a 16-byte stack frame."])
    code := Impl.Sm4.AArch64.ecbCall .encrypt Proof.Sm4.AArch64.ecbAnyFramed
    contract := Spec.Sm4.ecbEncryptContract AArch64.abi 3184
    stack := 3184
    ofSig := by exact (⟨_, _, _, by unfold Spec.Sm4.ecbEncryptContract Spec.Sm4.ecbContract; rfl⟩)
    verified := Proof.Sm4.AArch64.ecbCall_verified .encrypt
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sm4.ecbDecryptApi with
    target := AArch64.target
    doc := Spec.Sm4.ecbDecryptApi.doc
      (notes := ["Baseline AArch64: calls `vg_sm4_ecb` with `decrypt = 1`, saving the link register in a 16-byte stack frame."])
    code := Impl.Sm4.AArch64.ecbCall .decrypt Proof.Sm4.AArch64.ecbAnyFramed
    contract := Spec.Sm4.ecbDecryptContract AArch64.abi 3184
    stack := 3184
    ofSig := by exact (⟨_, _, _, by unfold Spec.Sm4.ecbDecryptContract Spec.Sm4.ecbContract; rfl⟩)
    verified := Proof.Sm4.AArch64.ecbCall_verified .decrypt
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Sm4.AArch64
