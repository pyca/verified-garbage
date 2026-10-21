module

public import VerifiedGarbage.Impl.Bignum.Arm.DownRow
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Bignum.Arm.DownRow
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import Init.Prelude
meta import Init.Prelude
public import VerifiedGarbage.TCB.Code
meta import VerifiedGarbage.TCB.Code

/-! Downward-write rows reveal only their public pointers and count. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.DownRow
open VG VG.Arm

theorem code_ct : ConstantTime isa (fun _ => True)
    (fun s t => s.gpr .r0=t.gpr .r0 ∧ s.gpr .r12=t.gpr .r12 ∧ s.gpr .lr=t.gpr .lr)
    VG.Impl.Bignum.Arm.DownRow.code := by
  refine VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.r0,.r12,.lr]) ?_ (by taint_decide)
  intro s t _ _ ⟨h0,h12,hcount⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact h0
  · exact h12
  · exact hcount

end VG.Proof.Bignum.Arm.DownRow
