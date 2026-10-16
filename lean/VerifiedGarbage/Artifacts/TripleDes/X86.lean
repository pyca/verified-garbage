module

public import VerifiedGarbage.Proof.TripleDes.X86.Frame
public import VerifiedGarbage.Proof.TripleDes.X86.VerifiedBlock
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.X86.FunctionsLit

@[expose] public section

namespace VG.Artifacts.TripleDes.X86

def artifacts : List Artifact := [
  Spec.TripleDes.expandKeyApi.artifact X86.target {
    notes := ["Baseline IA-32 scalar key expansion with fixed permutations and public round-count branches."]
    code := Impl.StackScratch.X86.withStackScratchWiped 532 3 128 Impl.TripleDes.X86.Key.expandKey
    stack := 532
    verified := Proof.TripleDes.X86.expandKey_framed },
  Spec.TripleDes.encryptBlockApi.artifact X86.target {
    notes := ["Baseline IA-32 scalar Boolean S-box circuits; IP and FP shared across all three DES passes."]
    code := Impl.TripleDes.X86.encryptBlock
    stack := 0
    verified := Proof.TripleDes.X86.encrypt_verified },
  Spec.TripleDes.decryptBlockApi.artifact X86.target {
    notes := ["Baseline IA-32 scalar Boolean S-box circuits with reverse EDE key order."]
    code := Impl.TripleDes.X86.decryptBlock
    stack := 0
    verified := Proof.TripleDes.X86.decrypt_verified },
  Spec.TripleDes.ecbEncryptApi.artifact X86.target {
    notes := ["Baseline IA-32, calling the verified Triple DES block primitive for each complete block."]
    code := Impl.StackScratch.X86.withStackScratchWiped 1044 3 256 Impl.TripleDes.X86.Ecb.encrypt
    stack := 1060
    verified := Proof.TripleDes.X86.ecb_framed .encrypt },
  Spec.TripleDes.ecbDecryptApi.artifact X86.target {
    notes := ["Baseline IA-32, calling the verified Triple DES block primitive for each complete block."]
    code := Impl.StackScratch.X86.withStackScratchWiped 1044 3 256 Impl.TripleDes.X86.Ecb.decrypt
    stack := 1060
    verified := Proof.TripleDes.X86.ecb_framed .decrypt }]

end VG.Artifacts.TripleDes.X86
