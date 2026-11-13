module

public import VerifiedGarbage.Impl.Rsa.Arm.Inverse
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Rsa.Arm.Inverse
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # `inverse` on ARMv7 is constant time, either variant: its addresses and branches depend only on `r7`–`r9` -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Impl.Rsa.Arm.Keys

theorem inverse_ct {um : Bool} : ConstantTime isa (fun _ => True)
    (fun s t => s.gpr .r7 = t.gpr .r7 ∧ s.gpr .r8 = t.gpr .r8 ∧ s.gpr .r9 = t.gpr .r9) (inverse um) := by
  have agree : ∀ s t : State, True → True → s.gpr .r7 = t.gpr .r7 ∧ s.gpr .r8 = t.gpr .r8 ∧ s.gpr .r9 = t.gpr .r9 →
      taint.Agree (Taint.ofRegs [.r7, .r8, .r9]) s t := by
    intro s t _ _ ⟨h7, h8, h9⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h7
    · exact h8
    · exact h9
  cases um
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r7, .r8, .r9]) agree (by taint_decide)
  · exact VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r7, .r8, .r9]) agree (by taint_decide)

end VG.Proof.Rsa.Arm.Keys
