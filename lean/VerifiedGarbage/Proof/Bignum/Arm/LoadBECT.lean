module

public import VerifiedGarbage.Impl.Bignum.Arm.LoadBE
meta import VerifiedGarbage.Impl.Bignum.Arm.LoadBE
public import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Zero-extended integer import reveals only pointers and lengths -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem loadBE_ct : ConstantTime isa (fun _ => True)
    (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r4 = t.gpr .r4 ∧ s.gpr .r5 = t.gpr .r5 ∧
      s.gpr .r6 = t.gpr .r6 ∧ s.gpr .lr = t.gpr .lr) loadBE := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r4, .r5, .r6, .lr]) ?_ (by taint_decide)
  intro s t _ _ h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2

end VG.Proof.Bignum.Arm
