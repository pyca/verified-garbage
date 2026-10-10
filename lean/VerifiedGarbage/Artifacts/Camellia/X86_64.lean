import VerifiedGarbage.Proof.Camellia.X86_64.Verified
import VerifiedGarbage.Proof.Camellia.X86_64.KeyVerified

namespace VG.Artifacts.Camellia.X86_64

def artifacts : List Artifact := [
  { Spec.Camellia.expandKeyApi with
    target := X86_64.target
    doc := Spec.Camellia.expandKeyApi.doc
      (notes := ["Baseline x86-64: `KA` and `KB` by the bitsliced rounds of the block functions, on eight copies of the value; the subkeys as rotations of 64-bit words."])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3216 .rcx 401 Impl.Camellia.X86_64.expandKey
    contract := Spec.Camellia.expandKeyContract X86_64.abi 3216
    stack := 3216
    verified := Proof.Camellia.X86_64.expandKey_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Camellia.ecbEncryptApi with
    target := X86_64.target
    doc := Spec.Camellia.ecbEncryptApi.doc
      (notes := ["Bitsliced on baseline x86-64: 8 blocks at a time in general-purpose registers, copied through a buffer on the stack, each half as eight 64-bit planes, the S-boxes as Boolean circuits."])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3216 .r8 401
      (Impl.Camellia.X86_64.ecb .encrypt)
    contract := Spec.Camellia.ecbEncryptContract X86_64.abi 3216
    stack := 3216
    ofSig := ⟨_, _, _, by unfold Spec.Camellia.ecbEncryptContract Spec.Camellia.ecbContract; rfl⟩
    verified := Proof.Camellia.X86_64.ecb_framed .encrypt
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Camellia.ecbDecryptApi with
    target := X86_64.target
    doc := Spec.Camellia.ecbDecryptApi.doc
      (notes := ["Bitsliced on baseline x86-64: 8 blocks at a time in general-purpose registers, copied through a buffer on the stack, each half as eight 64-bit planes, the S-boxes as Boolean circuits; the subkeys bitsliced in decryption's order, then encryption's rounds."])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3216 .r8 401
      (Impl.Camellia.X86_64.ecb .decrypt)
    contract := Spec.Camellia.ecbDecryptContract X86_64.abi 3216
    stack := 3216
    ofSig := ⟨_, _, _, by unfold Spec.Camellia.ecbDecryptContract Spec.Camellia.ecbContract; rfl⟩
    verified := Proof.Camellia.X86_64.ecb_framed .decrypt
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Camellia.X86_64
