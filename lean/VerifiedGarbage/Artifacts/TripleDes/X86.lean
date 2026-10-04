import VerifiedGarbage.Proof.TripleDes.X86.VerifiedBlock
import VerifiedGarbage.Proof.TripleDes.X86.Key.Verified
import VerifiedGarbage.Proof.TripleDes.X86.Ecb.Verified
import VerifiedGarbage.Proof.TripleDes.X86.Frame

namespace VG.Artifacts.TripleDes.X86

def artifacts : List Artifact := [
  { Spec.TripleDes.expandKeyApi with
    target := X86.target
    doc := Spec.TripleDes.expandKeyApi.doc
      (notes := ["Baseline IA-32 scalar key expansion with fixed permutations and public round-count branches."])
    code := Impl.StackScratch.X86.withStackScratchWiped 532 3 128 Impl.TripleDes.X86.Key.expandKey
    contract := Spec.TripleDes.expandKeyContract X86.abi 532
    stack := 532
    verified := Proof.TripleDes.X86.expandKey_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.TripleDes.encryptBlockApi with
    target := X86.target
    doc := Spec.TripleDes.encryptBlockApi.doc
      (notes := ["Baseline IA-32 scalar Boolean S-box circuits; IP and FP shared across all three DES passes."])
    code := Impl.TripleDes.X86.encryptBlock
    contract := Spec.TripleDes.encryptBlockContract X86.abi
    stack := 0
    verified := Proof.TripleDes.X86.encrypt_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.TripleDes.decryptBlockApi with
    target := X86.target
    doc := Spec.TripleDes.decryptBlockApi.doc
      (notes := ["Baseline IA-32 scalar Boolean S-box circuits with reverse EDE key order."])
    code := Impl.TripleDes.X86.decryptBlock
    contract := Spec.TripleDes.decryptBlockContract X86.abi
    stack := 0
    verified := Proof.TripleDes.X86.decrypt_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.TripleDes.ecbEncryptApi with
    target := X86.target
    doc := Spec.TripleDes.ecbEncryptApi.doc
      (notes := ["Baseline IA-32, calling the verified Triple DES block primitive for each complete block."])
    code := Impl.StackScratch.X86.withStackScratchWiped 1044 3 256 Impl.TripleDes.X86.Ecb.encrypt
    contract := Spec.TripleDes.ecbEncryptContract X86.abi 1060
    stack := 1060
    ofSig := ⟨_, _, _, by unfold Spec.TripleDes.ecbEncryptContract Spec.TripleDes.ecbContract; rfl⟩
    verified := Proof.TripleDes.X86.ecb_framed .encrypt
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.TripleDes.ecbDecryptApi with
    target := X86.target
    doc := Spec.TripleDes.ecbDecryptApi.doc
      (notes := ["Baseline IA-32, calling the verified Triple DES block primitive for each complete block."])
    code := Impl.StackScratch.X86.withStackScratchWiped 1044 3 256 Impl.TripleDes.X86.Ecb.decrypt
    contract := Spec.TripleDes.ecbDecryptContract X86.abi 1060
    stack := 1060
    ofSig := ⟨_, _, _, by unfold Spec.TripleDes.ecbDecryptContract Spec.TripleDes.ecbContract; rfl⟩
    verified := Proof.TripleDes.X86.ecb_framed .decrypt
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.TripleDes.X86
