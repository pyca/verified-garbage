import VerifiedGarbage.Proof.Seed.AArch64.Frame

/-! # SEED artifacts on baseline AArch64 -/

namespace VG.Artifacts.Seed.AArch64

def artifacts : List Artifact := [
  { Spec.Seed.expandKeyApi with
    target := AArch64.target
    doc := Spec.Seed.expandKeyApi.doc
      (notes := ["Baseline AArch64: the 32 inputs of `G` from 64-bit rotations of the key, then `G` of sixteen at a time, bitsliced in general-purpose registers through the AES S-box circuit."])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 976 .x2 122 Impl.Seed.AArch64.expandKey
    contract := Spec.Seed.expandKeyContract AArch64.abi 976
    stack := 976
    verified := Proof.Seed.AArch64.expandKey_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Seed.ecbEncryptApi with
    target := AArch64.target
    doc := Spec.Seed.ecbEncryptApi.doc
      (notes := ["Baseline AArch64: sixteen blocks at a time, each `G` of a round bitsliced in general-purpose registers through the AES S-box circuit (SEED's S-boxes are affine maps of AES's), with no table lookups."])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 976 .x3 122 Impl.Seed.AArch64.encrypt
    contract := Spec.Seed.ecbEncryptContract AArch64.abi 976
    stack := 976
    ofSig := ⟨_, _, _, by unfold Spec.Seed.ecbEncryptContract Spec.Seed.ecbContract; rfl⟩
    verified := Proof.Seed.AArch64.encrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Seed.ecbDecryptApi with
    target := AArch64.target
    doc := Spec.Seed.ecbDecryptApi.doc
      (notes := ["Baseline AArch64: sixteen blocks at a time, each `G` of a round bitsliced in general-purpose registers through the AES S-box circuit (SEED's S-boxes are affine maps of AES's), with no table lookups."])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 976 .x3 122 Impl.Seed.AArch64.decrypt
    contract := Spec.Seed.ecbDecryptContract AArch64.abi 976
    stack := 976
    ofSig := ⟨_, _, _, by unfold Spec.Seed.ecbDecryptContract Spec.Seed.ecbContract; rfl⟩
    verified := Proof.Seed.AArch64.decrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Seed.AArch64
