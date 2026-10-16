module

public import VerifiedGarbage.Impl.Bignum.Arm.ShiftLeft
meta import VerifiedGarbage.Impl.Bignum.Arm.ShiftLeft
public import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Only the shiftLeft pointer and word count are public -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem shiftLeft_ct : ConstantTime isa (fun _ => True)
    (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.gpr .lr = t.gpr .lr) shiftLeft := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .lr]) ?_ (by taint_decide)
  intro s t _ _ h
  refine Taint.agree_ofRegs fun r hr => ?_
  have : r = .r0 ∨ r = .lr := by simpa using hr
  rcases this with rfl | rfl
  · exact h.1
  · exact h.2

end VG.Proof.Bignum.Arm
