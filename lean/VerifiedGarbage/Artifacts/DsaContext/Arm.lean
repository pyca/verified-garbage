module

import VerifiedGarbage.Proof.Dsa.Arm.ContextVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import Batteries.Logic
public import VerifiedGarbage.Impl.Dsa.Arm.Context
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Dsa.Arm.ContextVerified
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.ContextInit
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Csub
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Digit
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.DigitRow
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Inverse
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.MulRow
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Ops
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.PowerTwo
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Select
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Timing
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Zeros
public import VerifiedGarbage.Proof.Mont.Arm.Step
public import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.Arm.Dyn.ContextInit
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Csub
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Digit
import VerifiedGarbage.Proof.Mont.Arm.Dyn.DigitRow
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Inverse
import VerifiedGarbage.Proof.Mont.Arm.Dyn.MulRow
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Ops
import VerifiedGarbage.Proof.Mont.Arm.Dyn.PowerTwo
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Select
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Timing
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Zeros
import VerifiedGarbage.Proof.Mont.Arm.Step
import VerifiedGarbage.Proof.Mont.Read

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
