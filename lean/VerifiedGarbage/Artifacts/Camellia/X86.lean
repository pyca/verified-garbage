import VerifiedGarbage.Proof.Camellia.X86.Verified
import VerifiedGarbage.Proof.Camellia.X86.KeyVerified

/-! # Camellia artifacts on baseline x86 (32-bit) -/

namespace VG.Artifacts.Camellia.X86

def artifacts : List Artifact := [
  { Spec.Camellia.expandKeyApi with
    target := X86.target
    doc := Spec.Camellia.expandKeyApi.doc
      (notes := ["Baseline IA-32: `KA` and `KB` by the bitsliced rounds of the block functions, on eight copies of the value; the subkeys as rotations of 32-bit words."])
    code := Impl.StackScratch.X86.withStackScratchWiped 2708 3 672 Impl.Camellia.X86.expandKey
    contract := Spec.Camellia.expandKeyContract X86.abi 2708
    stack := 2708
    verified := Proof.Camellia.X86.expandKey_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Camellia.ecbEncryptApi with
    target := X86.target
    doc := Spec.Camellia.ecbEncryptApi.doc
      (notes := ["Bitsliced on baseline IA-32: 8 blocks at a time in general-purpose registers, copied through a buffer on the stack, each half as sixteen 32-bit planes, the S-boxes as Boolean circuits."])
    code := Impl.StackScratch.X86.withStackScratchWiped 2712 4 672 (Impl.Camellia.X86.ecb .encrypt)
    contract := Spec.Camellia.ecbEncryptContract X86.abi 2712
    stack := 2712
    ofSig := ⟨_, _, _, by unfold Spec.Camellia.ecbEncryptContract Spec.Camellia.ecbContract; rfl⟩
    verified := Proof.Camellia.X86.ecb_framed .encrypt
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Camellia.ecbDecryptApi with
    target := X86.target
    doc := Spec.Camellia.ecbDecryptApi.doc
      (notes := ["Bitsliced on baseline IA-32: 8 blocks at a time in general-purpose registers, copied through a buffer on the stack, each half as sixteen 32-bit planes, the S-boxes as Boolean circuits; the subkeys bitsliced in decryption's order, then encryption's rounds."])
    code := Impl.StackScratch.X86.withStackScratchWiped 2712 4 672 (Impl.Camellia.X86.ecb .decrypt)
    contract := Spec.Camellia.ecbDecryptContract X86.abi 2712
    stack := 2712
    ofSig := ⟨_, _, _, by unfold Spec.Camellia.ecbDecryptContract Spec.Camellia.ecbContract; rfl⟩
    verified := Proof.Camellia.X86.ecb_framed .decrypt
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Camellia.X86
