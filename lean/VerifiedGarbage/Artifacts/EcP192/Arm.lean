module

public import VerifiedGarbage.Proof.EcKey.Arm.P192.Scrub -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P192.Arm.Law

/-! # P-192 public keys (FIPS 186-5 §A.2) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcP192.Arm

open VG.Proof.P192.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P192.publicKeyApi.artifact Arm.target (Proof.EcKey.Arm.P192.Scrub.publicKeyReg hasLaw.law),
  Spec.EcKey.P192.publicKeyApi.artifact Arm.target (Proof.EcKey.Arm.P192.Scrub.publicKeyUReg hasLaw.law),
  Spec.EcKey.P192.inst.compressPublicKeyApi.artifact Arm.target Proof.EcKey.Arm.P192.Scrub.compressReg,
  Spec.EcKey.P192.inst.decompressPublicKeyApi.artifact Arm.target (Proof.EcKey.Arm.P192.Scrub.decompressReg hasLaw.law),
  Spec.EcKey.P192.inst.compressPublicKeyApi.artifact Arm.target Proof.EcKey.Arm.P192.Scrub.compressUReg,
  Spec.EcKey.P192.inst.decompressPublicKeyApi.artifact Arm.target (Proof.EcKey.Arm.P192.Scrub.decompressUReg hasLaw.law)]

end VG.Artifacts.EcP192.Arm
