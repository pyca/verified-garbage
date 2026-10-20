module

public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! Fixed local-frame accesses used by native key generation have public addresses. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem keyScalarArgs_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.scalarArgs) (fun _ _ => True) := by
  have derive : RelCT isa (fun _ _ => True)
      (.block [.dp .sub .lr .lr (.reg .r3), .dp .add .r3 .r0 (.reg .lr)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _; exact Taint.agree_ofRegs (by simp)
  have save : RelCT isa (fun s t => s.gpr .r12 = t.gpr .r12 ∧ s.sp = t.sp)
      (.block [.str .r3 .r12 16, .mov .r2 (.imm 0)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r12]) _ (by taint_decide)
    intro s t h
    exact Taint.agree_ofRegs (fun r hr => by simp only [List.mem_singleton] at hr; subst r; exact h.1)
  change RelCT isa _ (.block ([.ldrSp .r0 40, .ldrSp .r1 48, .ldrSp .lr 32, .ldrSp .r3 20] ++
    [.dp .sub .lr .lr (.reg .r3), .dp .add .r3 .r0 (.reg .lr)] ++ [.addSp .r12 0] ++
    [.str .r3 .r12 16, .mov .r2 (.imm 0)])) _
  have middle := relCT_keep_sp (derive.mono (fun _ _ _ => trivial) (fun _ _ h => h)) (fun _ _ h => h)
  exact RelCT.block_append ((RelCT.block_append ((RelCT.block_append
    ((stackLoads_ct [(.r0, 40), (.r1, 48), (.lr, 32), (.r3, 20)]).seq middle)).seq stackAddr_ct)).seq save)

theorem keyClearArgs_ct (slot : Nat) : RelCT isa (fun s t => s.sp = t.sp)
    (.block [.ldrSp .r0 slot, .ldrSp .lr 32, .mov .r2 (.imm 0)]) (fun _ _ => True) := by
  have zero : RelCT isa (fun _ _ => True) (.block [.mov .r2 (.imm 0)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _; exact Taint.agree_ofRegs (by simp)
  exact RelCT.block_append ((stackLoads_ct [(.r0, slot), (.lr, 32)]).seq
    (zero.mono (fun _ _ _ => trivial) (fun _ _ h => h)))

theorem keyMaskArgs_ct (slot : Nat) : RelCT isa (fun s t => s.sp = t.sp)
    (.block [.ldrSp .r0 slot, .ldrSp .lr 32, .ldrSp .r3 64, .mov .r2 (.imm 0), .dp .sub .r2 .r2 (.reg .r3)])
    (fun _ _ => True) := by
  have mask : RelCT isa (fun _ _ => True) (.block [.mov .r2 (.imm 0), .dp .sub .r2 .r2 (.reg .r3)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _; exact Taint.agree_ofRegs (by simp)
  exact RelCT.block_append ((stackLoads_ct [(.r0, slot), (.lr, 32), (.r3, 64)]).seq
    (mask.mono (fun _ _ _ => trivial) (fun _ _ h => h)))

theorem keyFinishStatus_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block [.ldrSp .r3 64, .mov .r0 (.imm 3), .dp .sub .r0 .r0 (.shifted .r3 .lsl 1)]) (fun _ _ => True) := by
  have result : RelCT isa (fun _ _ => True)
      (.block [.mov .r0 (.imm 3), .dp .sub .r0 .r0 (.shifted .r3 .lsl 1)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _; exact Taint.agree_ofRegs (by simp)
  exact RelCT.block_append ((loadStack_ct .r3 64).seq (result.mono (fun _ _ _ => trivial) (fun _ _ h => h)))

end VG.Proof.Ffdh.Arm
