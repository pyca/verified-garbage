module

public import VerifiedGarbage.Proof.EcKey.Arm.P521.Scrub -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P521.Arm.Law

/-! # P-521 public keys (FIPS 186-5 §A.2) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcP521.Arm

open VG.Proof.P521.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P521.inst.compressPublicKeyApi.artifact Arm.target Proof.EcKey.Arm.P521.Scrub.compressReg,
  Spec.EcKey.P521.inst.decompressPublicKeyApi.artifact Arm.target (Proof.EcKey.Arm.P521.Scrub.decompressReg hasLaw.law),
  Spec.EcKey.P521.publicKeyApi.artifact Arm.target (Proof.EcKey.Arm.P521.Scrub.publicKeyReg hasLaw.law),
  Spec.EcKey.P521.inst.compressPublicKeyApi.artifact Arm.target Proof.EcKey.Arm.P521.Scrub.compressUReg,
  Spec.EcKey.P521.inst.decompressPublicKeyApi.artifact Arm.target (Proof.EcKey.Arm.P521.Scrub.decompressUReg hasLaw.law),
  Spec.EcKey.P521.publicKeyApi.artifact Arm.target (Proof.EcKey.Arm.P521.Scrub.publicKeyUReg hasLaw.law)]

end VG.Artifacts.EcP521.Arm
