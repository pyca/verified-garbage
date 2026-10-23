module
public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw
public import VerifiedGarbage.Impl.Rsa.X86.RecoverRt
public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.TCB.X86.Target

import VerifiedGarbage.Proof.Rsa.X86.RvOperationTiming
import VerifiedGarbage.Proof.Rsa.X86.RvSatisfiable
import VerifiedGarbage.Proof.Rsa.X86.RvCorrect

/-! # Complete i686 certificate for RSA prime recovery -/

@[expose] public section
variable [rsaBatchLaw : VG.Proof.Rsa.X86.BatchLaw]
include rsaBatchLaw
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Impl.Rsa.X86.Recover

theorem verified : Verified target VG.Impl.Rsa.X86.RecoverRt.code (Spec.Rsa.recoverPrimesContract abi 96) :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.Rsa.X86.Recover
