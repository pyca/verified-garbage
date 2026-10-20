module

public import VerifiedGarbage.Impl.Ffdh.Arm.VettedCap
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.RegistersCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Ffdh.Arm.VettedCap
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! A recognized cap changes the trace only through its public classification. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedCap
open VG VG.Arm VG.Proof.Bignum.Arm

theorem choose_ct :
    RelCT isa (fun s t => s.gpr .r11 = t.gpr .r11)
      (VG.Impl.Ffdh.Arm.VettedCap.choose VG.Impl.Ffdh.Arm.VettedCap.choices) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r11]) _ (by taint_decide)
  intro s t h
  exact Taint.agree_ofRegs (by simpa using h)

theorem code_ct :
    RelCT isa (fun s t => s.gpr .r11 = t.gpr .r11 ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.VettedCap.code (fun _ _ => True) := by
  have load : RelCT isa (fun s t => s.gpr .r11 = t.gpr .r11 ∧ s.sp = t.sp)
      (.block VG.Impl.Ffdh.Arm.VettedCap.load)
      (fun s t => RegistersEqual [.r11] s t ∧ s.sp = t.sp) := by
    apply registers_keep_ct [.r11]
      ((RelCT.block_append ((loadStack_ct .r6 20).seq (loadStack_ct .r3 68))).mono (fun _ _ h => h.2) (fun _ _ _ => trivial))
      (fun _ _ h r hr => by simp only [List.mem_singleton] at hr; subst r; exact h.1)
      (fun _ _ h => h.2)
      (by intro r hr i hi; simp only [instrs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr hi; subst r; rcases hi with rfl | rfl <;> rfl)
      (by rfl)
  have choose := relCT_keep_sp (choose_ct.mono
    (P' := fun (s t : State) => RegistersEqual [.r11] s t ∧ s.sp = t.sp)
    (fun _ _ h => h.1 .r11 (by simp)) (fun _ _ h => h)) (fun _ _ h => h.2)
  have stores : RelCT isa (fun s t => s.gpr .r12 = t.gpr .r12 ∧ s.sp = t.sp)
      (.block [.str .r6 .r12 20, .str .r3 .r12 68]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r12]) _ (by taint_decide)
    intro s t h
    exact Taint.agree_ofRegs (by simpa using h.1)
  have save : RelCT isa (fun s t => s.sp = t.sp)
      (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.boundSave) (fun _ _ => True) :=
    RelCT.block_append (stackAddr_ct.seq stores)
  exact load.seq (choose.seq (save.mono (fun _ _ h => h) (fun _ _ h => h)))

end VG.Proof.Ffdh.Arm.VettedCap
