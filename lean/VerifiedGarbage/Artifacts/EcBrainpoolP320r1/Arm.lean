module

public import VerifiedGarbage.Proof.EcKey.Arm.BrainpoolP320r1.Scrub -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.BrainpoolP320r1.Arm.Law
public import VerifiedGarbage.Proof.Weierstrass.Law

/-! # brainpoolP320r1 public keys (FIPS 186-5 §A.2) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcBrainpoolP320r1.Arm

open VG.Proof.BrainpoolP320r1.Arm (hasLaw)
open VG.Proof.EcKey.Arm.BrainpoolP320r1.Scrub

def artifacts : List Artifact := [
  Spec.EcKey.BrainpoolP320r1.publicKeyApi.artifact Arm.target (publicKeyReg hasLaw.law),
  Spec.EcKey.BrainpoolP320r1.publicKeyApi.artifact Arm.target (publicKeyUReg hasLaw.law),
  Spec.EcKey.BrainpoolP320r1.inst.compressPublicKeyApi.artifact Arm.target compressReg,
  Spec.EcKey.BrainpoolP320r1.inst.decompressPublicKeyApi.artifact Arm.target (decompressReg hasLaw.law),
  Spec.EcKey.BrainpoolP320r1.inst.compressPublicKeyApi.artifact Arm.target compressUReg,
  Spec.EcKey.BrainpoolP320r1.inst.decompressPublicKeyApi.artifact Arm.target (decompressUReg hasLaw.law)]

end VG.Artifacts.EcBrainpoolP320r1.Arm
