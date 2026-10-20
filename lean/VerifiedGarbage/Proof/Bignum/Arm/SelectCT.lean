module

public import VerifiedGarbage.Impl.Bignum.Arm.Select
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Bignum.Arm.Select
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # ARMv7 Montgomery selection-loop leakage: pointers and the word count are public -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem selectRow_ct : ConstantTime isa (fun _ => True)
    (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r10 = t.gpr .r10 ∧ s.gpr .r12 = t.gpr .r12 ∧ s.gpr .lr = t.gpr .lr) selectRow := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r10, .r12, .lr]) ?_ (by taint_decide)
  intro s t _ _ ⟨h0, h10, h12, hcount⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h0
  · exact h10
  · exact h12
  · exact hcount

end VG.Proof.Bignum.Arm
