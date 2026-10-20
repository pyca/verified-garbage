module

public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.Ffdh.Arm.RegistersCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Impl.Bignum.Arm.CopyBytes
meta import VerifiedGarbage.Impl.Bignum.Arm.CopyBytes
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT

/-! The scalar byte loops depend on public pointers and counts; the byte
mask and copied entropy values do not affect their traces. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem keyPrefix_ct : RelCT isa (fun s t => RegistersEqual [.r0, .lr] s t)
    (VG.Impl.Ffdh.Arm.Domain.GenerateKey.unlessZero .lr
      (.loop (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.prefixStep) .ne)) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .lr]) _ (by taint_decide)
  intro s t h; exact Taint.agree_ofRegs h

theorem keyZeros_ct : RelCT isa (fun s t => RegistersEqual [.r0, .lr] s t)
    VG.Impl.Ffdh.Arm.Domain.GenerateKey.zeros (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .lr]) _ (by taint_decide)
  intro s t h; exact Taint.agree_ofRegs h

theorem keyCopy_ct : RelCT isa (fun s t => RegistersEqual [.r0, .r1, .lr] s t)
    (VG.Impl.Ffdh.Arm.Domain.GenerateKey.unlessZero .lr VG.Impl.Bignum.Arm.copyBytes) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r1, .lr]) _ (by taint_decide)
  intro s t h; exact Taint.agree_ofRegs h

theorem keyFirst_ct : RelCT isa (fun s t => RegistersEqual [.r0, .r1] s t ∧ s.sp = t.sp)
    (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.first) (fun _ _ => True) := by
  have load : RelCT isa (fun s t => RegistersEqual [.r0, .r1] s t ∧ s.sp = t.sp)
      (.block [.ldrb .r2 .r1 0]) (fun s t => RegistersEqual [.r0] s t ∧ s.sp = t.sp) := by
    apply registers_keep_ct [.r0] ?_ (fun _ _ h r hr => h.1 r (by simp only [List.mem_singleton] at hr; subst r; simp))
      (fun _ _ h => h.2) (by intro r hr i hi; simp only [instrs, List.mem_singleton] at hr hi; subst r; subst i; rfl) (by rfl)
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r1]) _ (by taint_decide)
    intro s t h
    exact Taint.agree_ofRegs (fun r hr => h.1 r (by simp only [List.mem_singleton] at hr; subst r; simp))
  have maskLoad : RelCT isa (fun s t => RegistersEqual [.r0] s t ∧ s.sp = t.sp)
      (.block [.ldrSp .r3 68]) (fun s t => RegistersEqual [.r0] s t ∧ s.sp = t.sp) := by
    apply registers_keep_ct [.r0] ((loadStack_ct .r3 68).mono (fun _ _ h => h.2) (fun _ _ _ => trivial))
      (fun _ _ h => h.1) (fun _ _ h => h.2)
      (by intro r hr i hi; simp only [instrs, List.mem_singleton] at hr hi; subst r; subst i; rfl) (by rfl)
  have store : RelCT isa (fun s t => RegistersEqual [.r0] s t ∧ s.sp = t.sp)
      (.block [.dp .and .r2 .r2 (.reg .r3), .strb .r2 .r0 0,
        .dp .add .r0 .r0 (.imm 1), .dp .add .r1 .r1 (.imm 1)]) (fun s t => s.sp = t.sp) := by
    apply relCT_keep_sp ?_ (fun _ _ h => h.2)
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h; exact Taint.agree_ofRegs h.1
  have sub : RelCT isa (fun _ _ => True) (.block [.dp .sub .lr .lr (.imm 1)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _; exact Taint.agree_ofRegs (by simp)
  change RelCT isa _ (.block ([.ldrb .r2 .r1 0] ++ [.ldrSp .r3 68] ++
    [.dp .and .r2 .r2 (.reg .r3), .strb .r2 .r0 0, .dp .add .r0 .r0 (.imm 1), .dp .add .r1 .r1 (.imm 1)] ++
    [.ldrSp .lr 20] ++ [.dp .sub .lr .lr (.imm 1)])) _
  exact RelCT.block_append ((RelCT.block_append ((RelCT.block_append ((RelCT.block_append (load.seq maskLoad)).seq store)).seq
    (loadStack_ct .lr 20))).seq (sub.mono (fun _ _ _ => trivial) (fun _ _ h => h)))

end VG.Proof.Ffdh.Arm
