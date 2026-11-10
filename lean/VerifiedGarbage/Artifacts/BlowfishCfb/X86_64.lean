module

public import VerifiedGarbage.Proof.Blowfish.X86_64.Scrub
import VerifiedGarbage.Proof.Blowfish.X86_64.ModesLit
import VerifiedGarbage.Proof.Blowfish.X86_64.FbFinalLit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # Blowfish-CFB64 on x86-64 -/

@[expose] public section

namespace VG.Artifacts.BlowfishCfb.X86_64

def artifacts : List Artifact := [
  Spec.Blowfish.cfbEncryptApi.artifact X86_64.target Proof.Blowfish.X86_64.Scrub.cfbEncryptReg,
  Spec.Blowfish.cfbDecryptApi.artifact X86_64.target Proof.Blowfish.X86_64.Scrub.cfbDecryptReg,
  Spec.Blowfish.cfbEncryptFinalApi.artifact X86_64.target Proof.Blowfish.X86_64.Scrub.cfbEncryptFinalReg,
  Spec.Blowfish.cfbDecryptFinalApi.artifact X86_64.target Proof.Blowfish.X86_64.Scrub.cfbDecryptFinalReg]

end VG.Artifacts.BlowfishCfb.X86_64
