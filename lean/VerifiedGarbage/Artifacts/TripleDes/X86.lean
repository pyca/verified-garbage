module

public import VerifiedGarbage.Proof.TripleDes.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.TripleDes.X86.FunctionsLit

/-! # Triple DES on x86 -/

@[expose] public section

namespace VG.Artifacts.TripleDes.X86

def artifacts : List Artifact := [
  Spec.TripleDes.expandKeyApi.artifact X86.target Proof.TripleDes.X86.Scrub.expandKeyReg,
  Spec.TripleDes.ecbEncryptApi.artifact X86.target Proof.TripleDes.X86.Scrub.ecbEncryptReg,
  Spec.TripleDes.ecbDecryptApi.artifact X86.target Proof.TripleDes.X86.Scrub.ecbDecryptReg]

end VG.Artifacts.TripleDes.X86
