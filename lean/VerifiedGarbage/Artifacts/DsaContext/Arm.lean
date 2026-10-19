module

import VerifiedGarbage.Proof.Dsa.Arm.ContextVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import Batteries.Logic
public import VerifiedGarbage.Impl.Dsa.Arm.Context
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.TCB.Arm.Target

/-! # One Montgomery context setup helper per DSA modulus width on ARMv7 -/

@[expose] public section
namespace VG.Artifacts.DsaContext.Arm

def helper (n : Nat)
    (v : Verified Arm.target (Impl.Dsa.Arm.Context.body n)
      (Spec.Dsa.MontContext.setupContract (Impl.Dsa.Arm.Context.layout n) Arm.abi)) : Artifact :=
  (Spec.Dsa.MontContext.api (Impl.Dsa.Arm.Context.layout n)).artifact Arm.target {
    notes := ["Computes the radix-2^16 negative inverse, one, and R² modulo the modulus. \
      Callee-saved registers reside in the unused result slot, apart from the arithmetic \
      helpers' register saves in the header."]
    code := Impl.Dsa.Arm.Context.body n
    verified := v }

def artifacts : List Artifact := [
  helper 3 (Proof.Dsa.Arm.Context.verified 3),
  helper 4 (Proof.Dsa.Arm.Context.verified 4),
  helper 16 (Proof.Dsa.Arm.Context.verified 16),
  helper 32 (Proof.Dsa.Arm.Context.verified 32),
  helper 48 (Proof.Dsa.Arm.Context.verified 48)]

end VG.Artifacts.DsaContext.Arm
