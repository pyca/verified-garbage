module

public import VerifiedGarbage.Impl.Bignum.Arm.MontInit
meta import VerifiedGarbage.Impl.Bignum.Arm.MontInit
public import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Initialization leaks only the temporary, accumulator, and packed-word count -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem montInit_ct : ConstantTime isa (fun _ => True)
    (fun s t => s.gpr .r5 = t.gpr .r5 ∧ s.gpr .r6 = t.gpr .r6 ∧ s.gpr .r7 = t.gpr .r7) montInit := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r5, .r6, .r7]) ?_ (by taint_decide)
  intro s t _ _ h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2

end VG.Proof.Bignum.Arm
