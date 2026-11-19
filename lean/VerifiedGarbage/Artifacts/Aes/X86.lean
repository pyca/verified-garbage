module

public import VerifiedGarbage.Proof.Aes.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print

/-! # AES (FIPS 197) on x86 -/

@[expose] public section

namespace VG.Artifacts.Aes.X86

def artifacts : List Artifact := [
  Spec.Aes.expandKeyApi.artifact X86.target Proof.Aes.X86.Scrub.scalarReg,
  Spec.Aes.expandKeyApi.artifact X86.target Proof.Aes.X86.Scrub.aesniReg]

end VG.Artifacts.Aes.X86
