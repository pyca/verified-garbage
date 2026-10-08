import VerifiedGarbage.Proof.Camellia.AArch64.Verified
import VerifiedGarbage.Proof.Camellia.AArch64.KeyVerified

namespace VG.Artifacts.Camellia.AArch64

def artifacts : List Artifact := [
  { Spec.Camellia.expandKeyApi with
    target := AArch64.target
    doc := Spec.Camellia.expandKeyApi.doc
      (notes := ["Baseline AArch64: `KA` and `KB` by the bitsliced rounds of the block functions, on eight copies of the value; the subkeys as rotations of 64-bit words."])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3152 .x3 394 Impl.Camellia.AArch64.expandKey
    contract := Spec.Camellia.expandKeyContract AArch64.abi 3152
    stack := 3152
    verified := Proof.Camellia.AArch64.expandKey_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Camellia.ecbEncryptApi with
    target := AArch64.target
    doc := Spec.Camellia.ecbEncryptApi.doc
      (notes := ["Bitsliced on baseline AArch64: 8 blocks at a time in general-purpose registers, copied through a buffer on the stack, each half as eight 64-bit planes, the S-boxes as Boolean circuits."])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3152 .x4 394
      (Impl.Camellia.AArch64.ecb .encrypt)
    contract := Spec.Camellia.ecbEncryptContract AArch64.abi 3152
    stack := 3152
    ofSig := ⟨_, _, _, by unfold Spec.Camellia.ecbEncryptContract Spec.Camellia.ecbContract; rfl⟩
    verified := Proof.Camellia.AArch64.ecb_framed .encrypt
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Camellia.ecbDecryptApi with
    target := AArch64.target
    doc := Spec.Camellia.ecbDecryptApi.doc
      (notes := ["Bitsliced on baseline AArch64: 8 blocks at a time in general-purpose registers, copied through a buffer on the stack, each half as eight 64-bit planes, the S-boxes as Boolean circuits; the subkeys bitsliced in decryption's order, then encryption's rounds."])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3152 .x4 394
      (Impl.Camellia.AArch64.ecb .decrypt)
    contract := Spec.Camellia.ecbDecryptContract AArch64.abi 3152
    stack := 3152
    ofSig := ⟨_, _, _, by unfold Spec.Camellia.ecbDecryptContract Spec.Camellia.ecbContract; rfl⟩
    verified := Proof.Camellia.AArch64.ecb_framed .decrypt
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Camellia.AArch64
