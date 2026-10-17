module

public import VerifiedGarbage.Impl.Bignum.Arm.Mul64
meta import VerifiedGarbage.Impl.Bignum.Arm.Mul64
public import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Register-pair multiplication has no secret-dependent trace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem mul64_ct : ConstantTime isa (fun _ => True) (fun _ _ => True) (.block mul64) := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs []) ?_ (by taint_decide)
  intro s t _ _ _
  exact Taint.agree_ofRegs (by simp)

end VG.Proof.Bignum.Arm
