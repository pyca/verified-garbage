import VerifiedGarbage.Proof.TripleDes.Arm.VerifiedBlock
import VerifiedGarbage.Proof.TripleDes.Arm.Key.Verified
import VerifiedGarbage.Proof.TripleDes.Arm.Ecb.Verified
import VerifiedGarbage.Proof.TripleDes.Arm.Frame

namespace VG.Artifacts.TripleDes.Arm

def artifacts : List Artifact := [
  { Spec.TripleDes.expandKeyApi with
    target := Arm.target
    doc := Spec.TripleDes.expandKeyApi.doc
      (notes := ["Baseline ARMv7 scalar key expansion with fixed permutations and public round-count branches."])
    code := Impl.StackScratch.Arm.withRegScratchWiped 512 .r3 128 Impl.TripleDes.Arm.Key.expandKey
    contract := Spec.TripleDes.expandKeyContract Arm.abi 512
    stack := 512
    verified := Proof.TripleDes.Arm.expandKey_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.TripleDes.encryptBlockApi with
    target := Arm.target
    doc := Spec.TripleDes.encryptBlockApi.doc
      (notes := ["Baseline ARMv7 scalar Boolean S-box circuits; IP and FP shared across all three DES passes."])
    code := Impl.TripleDes.Arm.encryptBlock
    contract := Spec.TripleDes.encryptBlockContract Arm.abi
    stack := 0
    verified := Proof.TripleDes.Arm.encrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.TripleDes.decryptBlockApi with
    target := Arm.target
    doc := Spec.TripleDes.decryptBlockApi.doc
      (notes := ["Baseline ARMv7 scalar Boolean S-box circuits with reverse EDE key order."])
    code := Impl.TripleDes.Arm.decryptBlock
    contract := Spec.TripleDes.decryptBlockContract Arm.abi
    stack := 0
    verified := Proof.TripleDes.Arm.decrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.TripleDes.ecbEncryptApi with
    target := Arm.target
    doc := Spec.TripleDes.ecbEncryptApi.doc
      (notes := ["Baseline ARMv7, calling the verified Triple DES block primitive for each complete block."])
    code := Impl.StackScratch.Arm.withRegScratchWiped 1024 .r3 256 Impl.TripleDes.Arm.Ecb.encrypt
    contract := Spec.TripleDes.ecbEncryptContract Arm.abi 1024
    stack := 1024
    ofSig := ⟨_, _, _, by unfold Spec.TripleDes.ecbEncryptContract Spec.TripleDes.ecbContract; rfl⟩
    verified := Proof.TripleDes.Arm.ecb_framed Proof.TripleDes.Arm.Ecb.encrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.TripleDes.ecbDecryptApi with
    target := Arm.target
    doc := Spec.TripleDes.ecbDecryptApi.doc
      (notes := ["Baseline ARMv7, calling the verified Triple DES block primitive for each complete block."])
    code := Impl.StackScratch.Arm.withRegScratchWiped 1024 .r3 256 Impl.TripleDes.Arm.Ecb.decrypt
    contract := Spec.TripleDes.ecbDecryptContract Arm.abi 1024
    stack := 1024
    ofSig := ⟨_, _, _, by unfold Spec.TripleDes.ecbDecryptContract Spec.TripleDes.ecbContract; rfl⟩
    verified := Proof.TripleDes.Arm.ecb_framed Proof.TripleDes.Arm.Ecb.decrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.TripleDes.Arm
