module

public import VerifiedGarbage.Proof.TripleDes.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.TripleDes.X86.FbFinalLit
import VerifiedGarbage.Proof.TripleDes.X86.FbLit

/-! # Triple DES-CFB64 on x86 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb.X86

def artifacts : List Artifact := [
  Spec.TripleDes.cfbEncryptApi.artifact X86.target Proof.TripleDes.X86.Scrub.cfbEncryptReg,
  Spec.TripleDes.cfbDecryptApi.artifact X86.target Proof.TripleDes.X86.Scrub.cfbDecryptReg,
  Spec.TripleDes.cfbEncryptFinalApi.artifact X86.target Proof.TripleDes.X86.Scrub.cfbEncryptFinalReg,
  Spec.TripleDes.cfbDecryptFinalApi.artifact X86.target Proof.TripleDes.X86.Scrub.cfbDecryptFinalReg]

end VG.Artifacts.TripleDesCfb.X86
