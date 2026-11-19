module

public import VerifiedGarbage.Proof.EcKey.Arm.P256.Scrub -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P256.Arm.Law

/-! # P-256 public keys (FIPS 186-5 §A.2) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcP256.Arm

open VG.Proof.P256.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P256.inst.compressPublicKeyApi.artifact Arm.target Proof.EcKey.Arm.P256.Scrub.compressReg,
  Spec.EcKey.P256.inst.decompressPublicKeyApi.artifact Arm.target (Proof.EcKey.Arm.P256.Scrub.decompressReg hasLaw.law),
  Spec.EcKey.P256.inst.compressPublicKeyApi.artifact Arm.target Proof.EcKey.Arm.P256.Scrub.compressUReg,
  Spec.EcKey.P256.inst.decompressPublicKeyApi.artifact Arm.target (Proof.EcKey.Arm.P256.Scrub.decompressUReg hasLaw.law),
  Spec.EcKey.P256.publicKeyApi.artifact Arm.target (Proof.EcKey.Arm.P256.Scrub.publicKeyReg hasLaw.law),
  Spec.EcKey.P256.publicKeyApi.artifact Arm.target (Proof.EcKey.Arm.P256.Scrub.publicKeyUReg hasLaw.law)]

end VG.Artifacts.EcP256.Arm
