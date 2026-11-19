module

public import VerifiedGarbage.Proof.Camellia.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Camellia.X86.FbLit
import VerifiedGarbage.Proof.Camellia.X86.FbFinalLit

/-! # Camellia-CFB128 on x86 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCfb.X86

def artifacts : List Artifact := [
  Spec.Camellia.cfbEncryptApi.artifact X86.target Proof.Camellia.X86.Scrub.cfbEncryptReg,
  Spec.Camellia.cfbDecryptApi.artifact X86.target Proof.Camellia.X86.Scrub.cfbDecryptReg,
  Spec.Camellia.cfbEncryptFinalApi.artifact X86.target Proof.Camellia.X86.Scrub.cfbEncryptFinalReg,
  Spec.Camellia.cfbDecryptFinalApi.artifact X86.target Proof.Camellia.X86.Scrub.cfbDecryptFinalReg]

end VG.Artifacts.CamelliaCfb.X86
