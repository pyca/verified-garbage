module

public import VerifiedGarbage.Proof.EcKey.Arm.Secp256k1.Scrub -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.Secp256k1.Arm.Law

/-! # secp256k1 public keys (FIPS 186-5 §A.2) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcSecp256k1.Arm

open VG.Proof.Secp256k1.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.Secp256k1.inst.compressPublicKeyApi.artifact Arm.target Proof.EcKey.Arm.Secp256k1.Scrub.compressReg,
  Spec.EcKey.Secp256k1.inst.decompressPublicKeyApi.artifact Arm.target (Proof.EcKey.Arm.Secp256k1.Scrub.decompressReg hasLaw.law),
  Spec.EcKey.Secp256k1.inst.compressPublicKeyApi.artifact Arm.target Proof.EcKey.Arm.Secp256k1.Scrub.compressUReg,
  Spec.EcKey.Secp256k1.inst.decompressPublicKeyApi.artifact Arm.target (Proof.EcKey.Arm.Secp256k1.Scrub.decompressUReg hasLaw.law),
  Spec.EcKey.Secp256k1.publicKeyApi.artifact Arm.target (Proof.EcKey.Arm.Secp256k1.Scrub.publicKeyReg hasLaw.law),
  Spec.EcKey.Secp256k1.publicKeyApi.artifact Arm.target (Proof.EcKey.Arm.Secp256k1.Scrub.publicKeyUReg hasLaw.law)]

end VG.Artifacts.EcSecp256k1.Arm
