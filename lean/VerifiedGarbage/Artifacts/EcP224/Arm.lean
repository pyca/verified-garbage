module

public import VerifiedGarbage.Proof.EcKey.Arm.P224.Scrub -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P224.Arm.Law

/-! # P-224 public keys (FIPS 186-5 §A.2) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcP224.Arm

open VG.Proof.P224.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P224.inst.compressPublicKeyApi.artifact Arm.target Proof.EcKey.Arm.P224.Scrub.compressReg,
  Spec.EcKey.P224.inst.decompressPublicKeyApi.artifact Arm.target (Proof.EcKey.Arm.P224.Scrub.decompressReg hasLaw.law),
  Spec.EcKey.P224.inst.compressPublicKeyApi.artifact Arm.target Proof.EcKey.Arm.P224.Scrub.compressUReg,
  Spec.EcKey.P224.inst.decompressPublicKeyApi.artifact Arm.target (Proof.EcKey.Arm.P224.Scrub.decompressUReg hasLaw.law),
  Spec.EcKey.P224.publicKeyApi.artifact Arm.target (Proof.EcKey.Arm.P224.Scrub.publicKeyReg hasLaw.law),
  Spec.EcKey.P224.publicKeyApi.artifact Arm.target (Proof.EcKey.Arm.P224.Scrub.publicKeyUReg hasLaw.law)]

end VG.Artifacts.EcP224.Arm
