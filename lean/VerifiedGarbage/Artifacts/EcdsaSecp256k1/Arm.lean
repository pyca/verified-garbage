module

public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Secp256k1.CombCT
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Secp256k1.CombMain
public import VerifiedGarbage.Spec.Ecdsa.Verify.Secp256k1
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Secp256k1.CombVerified -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.Scrub
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.Secp256k1.Arm.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Secp256k1Comb

/-! # ECDSA over secp256k1 (FIPS 186-5) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcdsaSecp256k1.Arm

open VG.Proof.Secp256k1.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.Secp256k1.verifyHashApi.artifact Arm.target (Proof.Ecdsa.Arm.Secp256k1.Scrub.verifyReg hasLaw.law),
  Spec.Ecdsa.Secp256k1.verifyHashApi.artifact Arm.target (Proof.Ecdsa.Arm.Secp256k1.Scrub.verifyUReg hasLaw.law),
  Spec.Ecdsa.Rfc6979.Curves.secp256k1SignApi.artifact Arm.target (Proof.Ecdsa.Arm.Secp256k1.Scrub.signReg hasLaw.law),
  Spec.Ecdsa.Rfc6979.Curves.secp256k1SignApi.artifact Arm.target (Proof.Ecdsa.Arm.Secp256k1.Scrub.signUReg hasLaw.law)]

end VG.Artifacts.EcdsaSecp256k1.Arm
