module

public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
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
meta import VerifiedGarbage.Proof.Ffdh.Arm.CheckFlag
import VerifiedGarbage.Proof.Bignum.Arm.ArrayCompareCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst

/-! ### `Ffdh.Arm.ChecksCT`, which this module and modules that import it used -/

section

/-! The comparison helpers share RSA's fixed-width constant-time arithmetic. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (wp_mov op2_imm Rest)

theorem compare_ct {base : BitVec 32} {len w a b : Nat} (ha : a < 8) (hb : b < 8) :
    RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      (VG.Impl.Bignum.Arm.arrayCompare a b) (fun _ _ => True) :=
  (arrayCompare_ct ha hb).mono (fun _ _ h => ⟨layoutReady h.1, layoutReady h.2.1, h.2.2⟩) (fun _ _ h => h)

theorem copy_ct {base : BitVec 32} {len w o a : Nat} (ho : o < 8) (ha : a < 8) :
    RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.copy o a) (fun _ _ => True) := by
  have init : RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      (.block [.mov .r11 (.imm 0)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have wp (s : State) (h : ArithmeticReady base len w s) :
      WP isa (.block [.mov .r11 (.imm 0)]) s (ArithmeticReady base len w) := by
    refine wp_mov (op2_imm (by decide)) fun t moved => WP.block_nil ?_
    have rest : Rest [.r11] s t := moved.rest (by simp)
    exact h.of_mem moved.mem rest ((rest.gpr .r0 (by simp)).trans h.ptr)
  unfold VG.Impl.Ffdh.Arm.copy
  exact relCT_chain init wp wp ((selectArray_ct ho ha ha).mono
    (fun _ _ h => ⟨(layoutReady h.1).toSelectArrayReady, (layoutReady h.2.1).toSelectArrayReady, h.2.2⟩)
    (fun _ _ h => h))

theorem greaterOne_ct {base : BitVec 32} {len w a : Nat} (ha : a < 8) :
    RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.greaterOne a) (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.greaterOne
  exact relCT_chain (smallConst_ct (base := base) (len := len) (w := w) 1
    (by decide : 7 < 8) (by decide) (by decide))
    (fun s h => WP.mono (smallConst_ok s 1 h (by decide : 7 < 8) (by decide) (by decide) (by decide)) fun _ k => k.1)
    (fun s h => WP.mono (smallConst_ok s 1 h (by decide : 7 < 8) (by decide) (by decide) (by decide)) fun _ k => k.1)
    (compare_ct (by decide : 7 < 8) ha)

end VG.Proof.Ffdh.Arm

end

end

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
