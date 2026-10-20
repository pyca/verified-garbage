module
public import VerifiedGarbage.Impl.Rsa.X86.Recover
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
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Impl.Rsa.X86.Recover

theorem verified : Verified target code (Spec.Rsa.recoverPrimesContract abi 20) :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.Rsa.X86.Recover
