import VerifiedGarbage.Proof.Seed.X86_64.Frame

/-! # SEED artifacts on baseline x86-64 -/

namespace VG.Artifacts.Seed.X86_64

def artifacts : List Artifact := [
  { Spec.Seed.expandKeyApi with
    target := X86_64.target
    doc := Spec.Seed.expandKeyApi.doc
      (notes := ["Baseline x86-64: the 32 inputs of `G` from 64-bit rotations of the key, then `G` of sixteen at a time, bitsliced in general-purpose registers through the AES S-box circuit."])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1064 .rdx 132 Impl.Seed.X86_64.expandKey
    contract := Spec.Seed.expandKeyContract X86_64.abi 1064
    stack := 1064
    verified := Proof.Seed.X86_64.expandKey_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Seed.ecbEncryptApi with
    target := X86_64.target
    doc := Spec.Seed.ecbEncryptApi.doc
      (notes := ["Baseline x86-64: sixteen blocks at a time, each `G` of a round bitsliced in general-purpose registers through the AES S-box circuit (SEED's S-boxes are affine maps of AES's), with no table lookups."])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1064 .rcx 132 Impl.Seed.X86_64.encrypt
    contract := Spec.Seed.ecbEncryptContract X86_64.abi 1064
    stack := 1064
    ofSig := ⟨_, _, _, by unfold Spec.Seed.ecbEncryptContract Spec.Seed.ecbContract; rfl⟩
    verified := Proof.Seed.X86_64.encrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Seed.ecbDecryptApi with
    target := X86_64.target
    doc := Spec.Seed.ecbDecryptApi.doc
      (notes := ["Baseline x86-64: sixteen blocks at a time, each `G` of a round bitsliced in general-purpose registers through the AES S-box circuit (SEED's S-boxes are affine maps of AES's), with no table lookups."])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1064 .rcx 132 Impl.Seed.X86_64.decrypt
    contract := Spec.Seed.ecbDecryptContract X86_64.abi 1064
    stack := 1064
    ofSig := ⟨_, _, _, by unfold Spec.Seed.ecbDecryptContract Spec.Seed.ecbContract; rfl⟩
    verified := Proof.Seed.X86_64.decrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Seed.X86_64
