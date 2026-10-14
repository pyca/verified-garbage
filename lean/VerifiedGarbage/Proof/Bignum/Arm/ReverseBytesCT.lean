module

public import VerifiedGarbage.Impl.Bignum.Arm.ReverseBytes
meta import VerifiedGarbage.Impl.Bignum.Arm.ReverseBytes
public import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Byte conversion reveals only pointers and length -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem reverseBytes_ct : ConstantTime isa (fun _ => True)
    (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .lr = t.gpr .lr) reverseBytes := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .lr]) ?_ (by taint_decide)
  intro s t _ _ h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2

end VG.Proof.Bignum.Arm
