module

public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Ffdh.Arm.ChecksCT
import VerifiedGarbage.Proof.Ffdh.Arm.Equal
import VerifiedGarbage.Proof.Ffdh.Arm.CheckFlag
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
meta import VerifiedGarbage.Impl.Ffdh.Arm.Checks
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Impl.Ffdh.Arm.Checks
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
meta import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Impl.Bignum.Arm.ArrayCompare
import VerifiedGarbage.Proof.Ffdh.Arm.Checks
meta import VerifiedGarbage.Proof.Ffdh.Arm.Checks

/-! Equality and flag combining do not disclose operand words. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (Operand)

theorem saveFlag_ct : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0)
    (.block VG.Impl.Ffdh.Arm.saveFlag) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
  intro s t h
  exact Taint.agree_ofRegs (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h)

theorem andFlag_ct : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0)
    (.block VG.Impl.Ffdh.Arm.andFlag) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
  intro s t h
  exact Taint.agree_ofRegs (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h)

theorem equalFinish_ct : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0)
    (.block [.ldr .r3 .r0 136, .dp .orr .r11 .r11 (.reg .r3), .dp .eor .r11 .r11 (.imm 1)]) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
  intro s t h
  exact Taint.agree_ofRegs (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h)

theorem equal_ct {base : BitVec 32} {len w a b : Nat} (ha : Operand a) (hb : Operand b) :
    RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.equal a b) (fun _ _ => True) := by
  let P := ArithmeticReady base len w
  have save : RelCT isa (fun s t => P s ∧ P t ∧ s.sp = t.sp) (.block VG.Impl.Ffdh.Arm.saveFlag) (fun _ _ => True) :=
    saveFlag_ct.mono (fun _ _ h => h.1.ptr.trans h.2.1.ptr.symm) (fun _ _ h => h)
  have finish : RelCT isa (fun s t => P s ∧ P t ∧ s.sp = t.sp)
      (.block [.ldr .r3 .r0 136, .dp .orr .r11 .r11 (.reg .r3), .dp .eor .r11 .r11 (.imm 1)]) (fun _ _ => True) :=
    equalFinish_ct.mono (fun _ _ h => h.1.ptr.trans h.2.1.ptr.symm) (fun _ _ h => h)
  have wpAB (s : State) (h : P s) := WP.mono (compare_ok s h ha.1 hb.1 ha.2.2 hb.2.2) fun _ k => k.1
  have wpBA (s : State) (h : P s) := WP.mono (compare_ok s h hb.1 ha.1 hb.2.2 ha.2.2) fun _ k => k.1
  have wpSave (s : State) (h : P s) := WP.mono (saveFlag_ok s h) fun _ k => k.1
  unfold VG.Impl.Ffdh.Arm.equal
  exact relCT_chain (compare_ct ha.1 hb.1) wpAB wpAB
    (relCT_chain save wpSave wpSave (relCT_chain (compare_ct hb.1 ha.1) wpBA wpBA finish))

end VG.Proof.Ffdh.Arm
