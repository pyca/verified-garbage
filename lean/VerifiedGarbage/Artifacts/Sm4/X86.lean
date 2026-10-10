import VerifiedGarbage.Proof.Sm4.X86.KeyVerified

/-! # SM4 artifacts on baseline x86 (32-bit) -/

namespace VG.Artifacts.Sm4.X86

def artifacts : List Artifact := [
  { Spec.Sm4.expandKeyApi with
    target := X86.target
    doc := Spec.Sm4.expandKeyApi.doc
      (notes := ["Baseline IA-32: the key schedule's rounds bitsliced in general-purpose registers, eight copies of the key at a time, through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups."])
    code := Impl.StackScratch.X86.withStackScratchWiped 1448 2 358 Impl.Sm4.X86.expandKey
    contract := Spec.Sm4.expandKeyContract X86.abi 1448
    stack := 1448
    verified := Proof.Sm4.X86.expandKey_framed
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Sm4.ecbEncryptApi with
    target := X86.target
    doc := Spec.Sm4.ecbEncryptApi.doc
      (notes := ["Baseline IA-32: eight blocks at a time, bitsliced in general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups."])
    code := Impl.StackScratch.X86.withStackScratchWiped 1452 3 358 (Impl.Sm4.X86.ecb .encrypt)
    contract := Spec.Sm4.ecbEncryptContract X86.abi 1452
    stack := 1452
    ofSig := ⟨_, _, _, by unfold Spec.Sm4.ecbEncryptContract Spec.Sm4.ecbContract; rfl⟩
    verified := Proof.Sm4.X86.ecb_framed .encrypt
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Sm4.ecbDecryptApi with
    target := X86.target
    doc := Spec.Sm4.ecbDecryptApi.doc
      (notes := ["Baseline IA-32: eight blocks at a time, bitsliced in general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups."])
    code := Impl.StackScratch.X86.withStackScratchWiped 1452 3 358 (Impl.Sm4.X86.ecb .decrypt)
    contract := Spec.Sm4.ecbDecryptContract X86.abi 1452
    stack := 1452
    ofSig := ⟨_, _, _, by unfold Spec.Sm4.ecbDecryptContract Spec.Sm4.ecbContract; rfl⟩
    verified := Proof.Sm4.X86.ecb_framed .decrypt
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.Sm4.X86
