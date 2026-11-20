module

public import VerifiedGarbage.Proof.Rsa.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print

/-! # RSA (RFC 8017) on x86 -/

@[expose] public section
namespace VG.Artifacts.Rsa.X86

def artifacts : List Artifact := [
  Spec.Rsa.recoverPrimesDetApi.artifact X86.target Proof.Rsa.X86.Scrub.recoverPrimesDetReg,
  Spec.Rsa.checkKeyApi.artifact X86.target Proof.Rsa.X86.Scrub.checkKeyReg,
  Spec.Rsa.crtValuesApi.artifact X86.target Proof.Rsa.X86.Scrub.crtValuesReg,
  Spec.Rsa.publicPrecomputeApi.artifact X86.target Proof.Rsa.X86.Scrub.publicPrecomputeReg,
  Spec.Rsa.privatePrecomputeApi.artifact X86.target Proof.Rsa.X86.Scrub.privatePrecomputeReg]

end VG.Artifacts.Rsa.X86
