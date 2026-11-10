module

public import VerifiedGarbage.Proof.Camellia.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Camellia.X86_64.ModesLit
import VerifiedGarbage.Proof.Camellia.X86_64.FbFinalLit

/-! # Camellia-CFB128 on x86-64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCfb.X86_64

def artifacts : List Artifact := [
  Spec.Camellia.cfbEncryptApi.artifact X86_64.target Proof.Camellia.X86_64.Scrub.cfbEncryptReg,
  Spec.Camellia.cfbDecryptApi.artifact X86_64.target Proof.Camellia.X86_64.Scrub.cfbDecryptReg,
  Spec.Camellia.cfbEncryptFinalApi.artifact X86_64.target Proof.Camellia.X86_64.Scrub.cfbEncryptFinalReg,
  Spec.Camellia.cfbDecryptFinalApi.artifact X86_64.target Proof.Camellia.X86_64.Scrub.cfbDecryptFinalReg]

end VG.Artifacts.CamelliaCfb.X86_64
