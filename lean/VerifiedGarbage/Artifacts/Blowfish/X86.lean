module

public import VerifiedGarbage.Proof.Blowfish.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Blowfish.X86.Lit

/-! # Blowfish on x86 -/

@[expose] public section

namespace VG.Artifacts.Blowfish.X86

def artifacts : List Artifact := [
  Spec.Blowfish.expandKeyApi.artifact X86.target Proof.Blowfish.X86.Scrub.expandKeyReg,
  Spec.Blowfish.ecbEncryptApi.artifact X86.target Proof.Blowfish.X86.Scrub.ecbEncryptReg,
  Spec.Blowfish.ecbDecryptApi.artifact X86.target Proof.Blowfish.X86.Scrub.ecbDecryptReg]

end VG.Artifacts.Blowfish.X86
