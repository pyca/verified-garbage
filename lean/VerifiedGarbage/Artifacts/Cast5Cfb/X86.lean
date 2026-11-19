module

public import VerifiedGarbage.Proof.Cast5.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Cast5.X86.ModesLit
import VerifiedGarbage.Proof.Cast5.X86.FbFinalLit

/-! # CAST5-CFB64 on x86 -/

@[expose] public section

namespace VG.Artifacts.Cast5Cfb.X86

def artifacts : List Artifact := [
  Spec.Cast5.cfbEncryptApi.artifact X86.target Proof.Cast5.X86.Scrub.cfbEncryptReg,
  Spec.Cast5.cfbDecryptApi.artifact X86.target Proof.Cast5.X86.Scrub.cfbDecryptReg,
  Spec.Cast5.cfbEncryptFinalApi.artifact X86.target Proof.Cast5.X86.Scrub.cfbEncryptFinalReg,
  Spec.Cast5.cfbDecryptFinalApi.artifact X86.target Proof.Cast5.X86.Scrub.cfbDecryptFinalReg]

end VG.Artifacts.Cast5Cfb.X86
