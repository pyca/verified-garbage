module

public import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP320r1.Scrub -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.BrainpoolP320r1.Arm.Law
public import VerifiedGarbage.Proof.Weierstrass.Law

/-! # ECDSA over brainpoolP320r1 (FIPS 186-5) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcdsaBrainpoolP320r1.Arm

open VG.Proof.BrainpoolP320r1.Arm (hasLaw)
open VG.Proof.Ecdsa.Arm.BrainpoolP320r1.Scrub

def artifacts : List Artifact := [
  Spec.Ecdsa.BrainpoolP320r1.verifyHashApi.artifact Arm.target (verifyReg hasLaw.law),
  Spec.Ecdsa.BrainpoolP320r1.verifyHashApi.artifact Arm.target (verifyUReg hasLaw.law),
  Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1SignApi.artifact Arm.target (signReg hasLaw.law),
  Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1SignApi.artifact Arm.target (signUReg hasLaw.law)]

end VG.Artifacts.EcdsaBrainpoolP320r1.Arm
