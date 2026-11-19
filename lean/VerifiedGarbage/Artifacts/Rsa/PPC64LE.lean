module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # RSA (RFC 8017) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Rsa.PPC64LE

def artifacts : List Artifact := [
  Spec.Rsa.publicPrecomputeApi.artifact PPC64LE.target Proof.Rsa.PPC64LE.Scrub.publicPrecomputeReg,
  Spec.Rsa.privatePrecomputeApi.artifact PPC64LE.target Proof.Rsa.PPC64LE.Scrub.privatePrecomputeReg,
  Spec.Rsa.crtValuesApi.artifact PPC64LE.target Proof.Rsa.PPC64LE.Scrub.crtValuesReg,
  Spec.Rsa.checkKeyApi.artifact PPC64LE.target Proof.Rsa.PPC64LE.Scrub.checkKeyReg,
  Spec.Rsa.recoverPrimesDetApi.artifact PPC64LE.target Proof.Rsa.PPC64LE.Scrub.recoverPrimesDetReg]

end VG.Artifacts.Rsa.PPC64LE
