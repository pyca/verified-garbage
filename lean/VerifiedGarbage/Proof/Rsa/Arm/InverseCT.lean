module

public import VerifiedGarbage.Impl.Rsa.Arm.Inverse
meta import VerifiedGarbage.Impl.Rsa.Arm.Inverse
public import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # `inverse` on ARMv7 is constant time: its addresses and branches depend only on `r7`–`r9` -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Impl.Rsa.Arm.Keys

theorem inverse_ct : ConstantTime isa (fun _ => True)
    (fun s t => s.gpr .r7 = t.gpr .r7 ∧ s.gpr .r8 = t.gpr .r8 ∧ s.gpr .r9 = t.gpr .r9) inverse := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r7, .r8, .r9]) ?_ (by taint_decide)
  intro s t _ _ ⟨h7, h8, h9⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h7
  · exact h8
  · exact h9

end VG.Proof.Rsa.Arm.Keys
