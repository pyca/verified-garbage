module

public import VerifiedGarbage.Proof.Sm4.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Sm4.X86_64.ModesLit
import VerifiedGarbage.Proof.Sm4.X86_64.FbFinalLit

/-! # SM4-CFB128 on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Sm4Cfb.X86_64

def artifacts : List Artifact := [
  Spec.Sm4.cfbEncryptApi.artifact X86_64.target Proof.Sm4.X86_64.Scrub.cfbEncryptReg,
  Spec.Sm4.cfbDecryptApi.artifact X86_64.target Proof.Sm4.X86_64.Scrub.cfbDecryptReg,
  Spec.Sm4.cfbEncryptFinalApi.artifact X86_64.target Proof.Sm4.X86_64.Scrub.cfbEncryptFinalReg,
  Spec.Sm4.cfbDecryptFinalApi.artifact X86_64.target Proof.Sm4.X86_64.Scrub.cfbDecryptFinalReg]

end VG.Artifacts.Sm4Cfb.X86_64
