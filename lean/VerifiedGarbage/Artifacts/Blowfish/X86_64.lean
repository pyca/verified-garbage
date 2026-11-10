module
import VerifiedGarbage.Proof.Blowfish.X86_64.ModesLit
import VerifiedGarbage.Proof.Blowfish.X86_64.Lit

public import VerifiedGarbage.Proof.Blowfish.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # Blowfish on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Blowfish.X86_64

def artifacts : List Artifact := [
  Spec.Blowfish.expandKeyApi.artifact X86_64.target Proof.Blowfish.X86_64.Scrub.expandKeyReg,
  Spec.Blowfish.ecbEncryptApi.artifact X86_64.target Proof.Blowfish.X86_64.Scrub.ecbEncryptReg,
  Spec.Blowfish.ecbDecryptApi.artifact X86_64.target Proof.Blowfish.X86_64.Scrub.ecbDecryptReg]

end VG.Artifacts.Blowfish.X86_64
