module

public import VerifiedGarbage.Proof.Camellia.Arm.Verified
public import VerifiedGarbage.Proof.Camellia.Arm.KeyVerified
import Mathlib.Tactic.SplitIfs

@[expose] public section

namespace VG.Artifacts.Camellia.Arm

def artifacts : List Artifact := [
  { Spec.Camellia.expandKeyApi with
    target := Arm.target
    doc := Spec.Camellia.expandKeyApi.doc
      (notes := ["Baseline ARMv7: `KA` and `KB` by the bitsliced rounds of the block functions, on eight copies of the value; the subkeys as rotations of 32-bit words."])
    code := Impl.StackScratch.Arm.withRegScratchWiped 2720 .r3 680 Impl.Camellia.Arm.expandKey
    contract := Spec.Camellia.expandKeyContract Arm.abi 2720
    stack := 2720
    verified := Proof.Camellia.Arm.expandKey_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Camellia.ecbEncryptApi with
    target := Arm.target
    doc := Spec.Camellia.ecbEncryptApi.doc
      (notes := ["Bitsliced on baseline ARMv7: 8 blocks at a time in general-purpose registers, copied through a buffer on the stack, each half as sixteen 32-bit planes, the S-boxes as Boolean circuits."])
    code := Impl.StackScratch.Arm.withStackScratchWiped 2816 0 680 (Impl.Camellia.Arm.ecb .encrypt)
    contract := Spec.Camellia.ecbEncryptContract Arm.abi 2816
    stack := 2816
    ofSig := by exact (⟨_, _, _, by unfold Spec.Camellia.ecbEncryptContract Spec.Camellia.ecbContract; rfl⟩)
    verified := Proof.Camellia.Arm.ecb_framed .encrypt
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Camellia.ecbDecryptApi with
    target := Arm.target
    doc := Spec.Camellia.ecbDecryptApi.doc
      (notes := ["Bitsliced on baseline ARMv7: 8 blocks at a time in general-purpose registers, copied through a buffer on the stack, each half as sixteen 32-bit planes, the S-boxes as Boolean circuits; the subkeys bitsliced in decryption's order, then encryption's rounds."])
    code := Impl.StackScratch.Arm.withStackScratchWiped 2816 0 680 (Impl.Camellia.Arm.ecb .decrypt)
    contract := Spec.Camellia.ecbDecryptContract Arm.abi 2816
    stack := 2816
    ofSig := by exact (⟨_, _, _, by unfold Spec.Camellia.ecbDecryptContract Spec.Camellia.ecbContract; rfl⟩)
    verified := Proof.Camellia.Arm.ecb_framed .decrypt
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Camellia.Arm
