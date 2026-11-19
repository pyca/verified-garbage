module

public import VerifiedGarbage.Proof.Camellia.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Camellia.X86.Lit

/-! # Camellia on x86 -/

@[expose] public section

namespace VG.Artifacts.Camellia.X86

def artifacts : List Artifact := [
  Spec.Camellia.expandKeyApi.artifact X86.target Proof.Camellia.X86.Scrub.expandKeyReg,
  Spec.Camellia.ecbEncryptApi.artifact X86.target Proof.Camellia.X86.Scrub.ecbEncryptReg,
  Spec.Camellia.ecbDecryptApi.artifact X86.target Proof.Camellia.X86.Scrub.ecbDecryptReg]

end VG.Artifacts.Camellia.X86
