module

public import VerifiedGarbage.Proof.EcKey.Arm.BrainpoolP256r1.Scrub -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.BrainpoolP256r1.Arm.Law

/-! # brainpoolP256r1 public keys (FIPS 186-5 §A.2) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcBrainpoolP256r1.Arm

open VG.Proof.BrainpoolP256r1.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.BrainpoolP256r1.publicKeyApi.artifact Arm.target (Proof.EcKey.Arm.BrainpoolP256r1.Scrub.publicKeyReg hasLaw.law),
  Spec.EcKey.BrainpoolP256r1.publicKeyApi.artifact Arm.target (Proof.EcKey.Arm.BrainpoolP256r1.Scrub.publicKeyUReg hasLaw.law),
  Spec.EcKey.BrainpoolP256r1.inst.compressPublicKeyApi.artifact Arm.target Proof.EcKey.Arm.BrainpoolP256r1.Scrub.compressReg,
  Spec.EcKey.BrainpoolP256r1.inst.decompressPublicKeyApi.artifact Arm.target (Proof.EcKey.Arm.BrainpoolP256r1.Scrub.decompressReg hasLaw.law),
  Spec.EcKey.BrainpoolP256r1.inst.compressPublicKeyApi.artifact Arm.target Proof.EcKey.Arm.BrainpoolP256r1.Scrub.compressUReg,
  Spec.EcKey.BrainpoolP256r1.inst.decompressPublicKeyApi.artifact Arm.target (Proof.EcKey.Arm.BrainpoolP256r1.Scrub.decompressUReg hasLaw.law)]

end VG.Artifacts.EcBrainpoolP256r1.Arm
