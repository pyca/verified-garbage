import VerifiedGarbage.Proof.Seed.X86.KeyVerified

/-! # SEED artifacts on baseline x86 (32-bit) -/

namespace VG.Artifacts.Seed.X86

def artifacts : List Artifact := [
  { Spec.Seed.expandKeyApi with
    target := X86.target
    doc := Spec.Seed.expandKeyApi.doc
      (notes := ["Baseline IA-32: the 32 inputs of `G` from the key words in the working space, then `G` of eight at a time, bitsliced in general-purpose registers through the AES S-box circuit (SEED's S-boxes are affine maps of AES's), with no table lookups."])
    code := Impl.StackScratch.X86.withStackScratchWiped 840 2 206 Impl.Seed.X86.expandKey
    contract := Spec.Seed.expandKeyContract X86.abi 840
    stack := 840
    verified := Proof.Seed.X86.expandKey_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Seed.ecbEncryptApi with
    target := X86.target
    doc := Spec.Seed.ecbEncryptApi.doc
      (notes := ["Baseline IA-32: eight blocks at a time, each `G` of a round bitsliced in general-purpose registers through the AES S-box circuit (SEED's S-boxes are affine maps of AES's), with no table lookups."])
    code := Impl.StackScratch.X86.withStackScratchWiped 844 3 206 (Impl.Seed.X86.ecb .encrypt)
    contract := Spec.Seed.ecbEncryptContract X86.abi 844
    stack := 844
    ofSig := ⟨_, _, _, by unfold Spec.Seed.ecbEncryptContract Spec.Seed.ecbContract; rfl⟩
    verified := Proof.Seed.X86.ecb_framed .encrypt
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Seed.ecbDecryptApi with
    target := X86.target
    doc := Spec.Seed.ecbDecryptApi.doc
      (notes := ["Baseline IA-32: eight blocks at a time, each `G` of a round bitsliced in general-purpose registers through the AES S-box circuit (SEED's S-boxes are affine maps of AES's), with no table lookups."])
    code := Impl.StackScratch.X86.withStackScratchWiped 844 3 206 (Impl.Seed.X86.ecb .decrypt)
    contract := Spec.Seed.ecbDecryptContract X86.abi 844
    stack := 844
    ofSig := ⟨_, _, _, by unfold Spec.Seed.ecbDecryptContract Spec.Seed.ecbContract; rfl⟩
    verified := Proof.Seed.X86.ecb_framed .decrypt
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Seed.X86
