module

public import VerifiedGarbage.Proof.Blowfish.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Blowfish.X86.ModesLit
import VerifiedGarbage.Proof.Blowfish.X86.FbFinalLit

/-! # Blowfish-CFB64 on x86 -/

@[expose] public section

namespace VG.Artifacts.BlowfishCfb.X86

def artifacts : List Artifact := [
  Spec.Blowfish.cfbEncryptApi.artifact X86.target Proof.Blowfish.X86.Scrub.cfbEncryptReg,
  Spec.Blowfish.cfbDecryptApi.artifact X86.target Proof.Blowfish.X86.Scrub.cfbDecryptReg,
  Spec.Blowfish.cfbEncryptFinalApi.artifact X86.target Proof.Blowfish.X86.Scrub.cfbEncryptFinalReg,
  Spec.Blowfish.cfbDecryptFinalApi.artifact X86.target Proof.Blowfish.X86.Scrub.cfbDecryptFinalReg]

end VG.Artifacts.BlowfishCfb.X86
