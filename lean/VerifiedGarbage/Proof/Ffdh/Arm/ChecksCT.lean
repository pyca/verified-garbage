module

import VerifiedGarbage.Proof.Ffdh.Arm.Checks
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.ArrayCompareCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
meta import VerifiedGarbage.Impl.Ffdh.Arm.Checks
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Impl.Ffdh.Arm.Checks
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
meta import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady

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
