module

public import VerifiedGarbage.Proof.Ecdh.Arm.BrainpoolP320r1.Scrub -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.BrainpoolP320r1.Arm.Law
public import VerifiedGarbage.Proof.Weierstrass.Law

/-! # ECDH over brainpoolP320r1 (SP 800-56A) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcdhBrainpoolP320r1.Arm

open VG.Proof.BrainpoolP320r1.Arm (hasLaw)
open VG.Proof.Ecdh.Arm.BrainpoolP320r1.Scrub

def artifacts : List Artifact := [
  Spec.Ecdh.BrainpoolP320r1.exchangeApi.artifact Arm.target (exchangeReg hasLaw.law),
  Spec.Ecdh.BrainpoolP320r1.exchangeApi.artifact Arm.target (exchangeUReg hasLaw.law)]

end VG.Artifacts.EcdhBrainpoolP320r1.Arm
