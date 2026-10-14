module

public import VerifiedGarbage.Proof.Bignum.Arm.InitInverse
public import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Bignum.Arm.InitInverse
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Inverse initialization uses only public memory addresses -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem initInverse_ct : ConstantTime isa (fun _ => True)
    (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r12 = t.gpr .r12) initInverse := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r12]) ?_ (by taint_decide)
  intro s t _ _ h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1
  · exact h.2

end VG.Proof.Bignum.Arm
