module

public import VerifiedGarbage.Proof.Cast5.X86_64.FbVerified
public import VerifiedGarbage.Proof.Cast5.X86_64.FbFinalVerified
import VerifiedGarbage.Proof.Cast5.X86_64.ModesLit
import VerifiedGarbage.Proof.Cast5.X86_64.FbFinalLit
public import VerifiedGarbage.Proof.Cast5.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # CAST5-CFB64 on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Cast5Cfb.X86_64

def artifacts : List Artifact := [
  Spec.Cast5.cfbEncryptApi.artifact X86_64.target Proof.Cast5.X86_64.Scrub.cfbEncryptReg,
  Spec.Cast5.cfbDecryptApi.artifact X86_64.target Proof.Cast5.X86_64.Scrub.cfbDecryptReg,
  Spec.Cast5.cfbEncryptFinalApi.artifact X86_64.target Proof.Cast5.X86_64.Scrub.cfbEncryptFinalReg,
  Spec.Cast5.cfbDecryptFinalApi.artifact X86_64.target Proof.Cast5.X86_64.Scrub.cfbDecryptFinalReg]

end VG.Artifacts.Cast5Cfb.X86_64
