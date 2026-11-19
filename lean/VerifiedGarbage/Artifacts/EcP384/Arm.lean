module

public import VerifiedGarbage.Proof.EcKey.Arm.P384.Scrub -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P384.Arm.Law

/-! # P-384 public keys (FIPS 186-5 §A.2) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcP384.Arm

open VG.Proof.P384.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P384.inst.compressPublicKeyApi.artifact Arm.target Proof.EcKey.Arm.P384.Scrub.compressReg,
  Spec.EcKey.P384.inst.decompressPublicKeyApi.artifact Arm.target (Proof.EcKey.Arm.P384.Scrub.decompressReg hasLaw.law),
  Spec.EcKey.P384.inst.compressPublicKeyApi.artifact Arm.target Proof.EcKey.Arm.P384.Scrub.compressUReg,
  Spec.EcKey.P384.inst.decompressPublicKeyApi.artifact Arm.target (Proof.EcKey.Arm.P384.Scrub.decompressUReg hasLaw.law),
  Spec.EcKey.P384.publicKeyApi.artifact Arm.target (Proof.EcKey.Arm.P384.Scrub.publicKeyReg hasLaw.law),
  Spec.EcKey.P384.publicKeyApi.artifact Arm.target (Proof.EcKey.Arm.P384.Scrub.publicKeyUReg hasLaw.law)]

end VG.Artifacts.EcP384.Arm
