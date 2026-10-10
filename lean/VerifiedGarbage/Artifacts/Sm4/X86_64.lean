import VerifiedGarbage.Proof.Sm4.X86_64.KeyVerified

/-! # SM4 artifacts on baseline x86-64 -/

namespace VG.Artifacts.Sm4.X86_64

def artifacts : List Artifact := [
  { Spec.Sm4.expandKeyApi with
    target := X86_64.target
    doc := Spec.Sm4.expandKeyApi.doc
      (notes := ["Baseline x86-64: the key schedule's rounds bitsliced in general-purpose registers, sixteen copies of the key at a time, through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups."])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3144 .rdx 392 Impl.Sm4.X86_64.expandKey
    contract := Spec.Sm4.expandKeyContract X86_64.abi 3144
    stack := 3144
    verified := Proof.Sm4.X86_64.expandKey_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Sm4.ecbEncryptApi with
    target := X86_64.target
    doc := Spec.Sm4.ecbEncryptApi.doc
      (notes := ["Baseline x86-64: sixteen blocks at a time, bitsliced in general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups."])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3144 .rcx 392 (Impl.Sm4.X86_64.ecb .encrypt)
    contract := Spec.Sm4.ecbEncryptContract X86_64.abi 3144
    stack := 3144
    ofSig := ⟨_, _, _, by unfold Spec.Sm4.ecbEncryptContract Spec.Sm4.ecbContract; rfl⟩
    verified := Proof.Sm4.X86_64.ecb_framed .encrypt
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Sm4.ecbDecryptApi with
    target := X86_64.target
    doc := Spec.Sm4.ecbDecryptApi.doc
      (notes := ["Baseline x86-64: sixteen blocks at a time, bitsliced in general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups."])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3144 .rcx 392 (Impl.Sm4.X86_64.ecb .decrypt)
    contract := Spec.Sm4.ecbDecryptContract X86_64.abi 3144
    stack := 3144
    ofSig := ⟨_, _, _, by unfold Spec.Sm4.ecbDecryptContract Spec.Sm4.ecbContract; rfl⟩
    verified := Proof.Sm4.X86_64.ecb_framed .decrypt
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Sm4.X86_64
