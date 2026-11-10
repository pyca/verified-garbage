module

public import VerifiedGarbage.Proof.Camellia.X86_64.Scrub
import VerifiedGarbage.Proof.Camellia.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # Camellia on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Camellia.X86_64

def artifacts : List Artifact := [
  Spec.Camellia.expandKeyApi.artifact X86_64.target Proof.Camellia.X86_64.Scrub.expandKeyReg,
  Spec.Camellia.ecbEncryptApi.artifact X86_64.target Proof.Camellia.X86_64.Scrub.ecbEncryptReg,
  Spec.Camellia.ecbDecryptApi.artifact X86_64.target Proof.Camellia.X86_64.Scrub.ecbDecryptReg]

end VG.Artifacts.Camellia.X86_64
