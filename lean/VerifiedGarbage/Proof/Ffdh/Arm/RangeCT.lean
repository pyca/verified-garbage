module

public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Ffdh.Arm.EqualCT
import VerifiedGarbage.Proof.Ffdh.Arm.Range
import VerifiedGarbage.Proof.Ffdh.Arm.SetLowBit
import VerifiedGarbage.Proof.Ffdh.Arm.SetLowBitCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Ffdh.Arm.Checks
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.BelowP
import VerifiedGarbage.Proof.Ffdh.Arm.CheckFlag
import VerifiedGarbage.Proof.Ffdh.Arm.Checks
import VerifiedGarbage.Proof.Ffdh.Arm.ChecksCT

/-! Full-width range checks have the same trace for different secret values. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (Operand)

theorem belowP_ready (s : State) {base : BitVec 32} {len w a : Nat}
    (h : ArithmeticReady base len w s) (ha : a < 8) :
    WP isa (VG.Impl.Ffdh.Arm.belowP a) s (ArithmeticReady base len w) := by
  rw [VG.Impl.Ffdh.Arm.belowP, WP.seq_iff]
  refine WP.mono (copy_ok s h (by decide : 7 < 8) ha (by decide)) ?_
  rintro u ⟨readyU, _⟩
  rw [WP.seq_iff]
  refine WP.mono (setLowBit_ok u readyU) ?_
  rintro v ⟨readyV, _⟩
  exact WP.mono (compare_ok v readyV (by decide : 7 < 8) (by decide : 0 < 8) (by decide) (by decide)) fun _ k => k.1

theorem belowP_ct {base : BitVec 32} {len w a : Nat} (ha : a < 8) :
    RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.belowP a) (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.belowP
  exact relCT_chain (copy_ct (by decide : 7 < 8) ha)
    (fun s h => WP.mono (copy_ok s h (by decide : 7 < 8) ha (by decide)) fun _ k => k.1)
    (fun s h => WP.mono (copy_ok s h (by decide : 7 < 8) ha (by decide)) fun _ k => k.1)
    (relCT_chain setLowBit_ct
      (fun s h => WP.mono (setLowBit_ok s h) fun _ k => k.1)
      (fun s h => WP.mono (setLowBit_ok s h) fun _ k => k.1)
      (compare_ct (by decide : 7 < 8) (by decide : 0 < 8)))

theorem inRange_ready (s : State) {base : BitVec 32} {len w a : Nat}
    (h : ArithmeticReady base len w s) (ha : Operand a) (na7 : a ≠ 7) :
    WP isa (VG.Impl.Ffdh.Arm.inRange a) s (ArithmeticReady base len w) := by
  rw [VG.Impl.Ffdh.Arm.inRange, WP.seq_iff]
  refine WP.mono (greaterOne_ok s h ha.1 ha.2.2 na7 ha) ?_
  rintro u ⟨readyU, _⟩
  rw [WP.seq_iff]
  refine WP.mono (saveFlag_ok u readyU) ?_
  rintro v ⟨readyV, _⟩
  rw [WP.seq_iff]
  refine WP.mono (belowP_ready v readyV ha.1) ?_
  intro t readyT
  refine WP.mono (andFlag_ok t readyT) ?_
  rintro z ⟨⟨_, mem⟩, rest⟩
  exact readyT.of_mem mem rest ((rest.gpr .r0 (by simp)).trans readyT.ptr)

theorem inRange_ct {base : BitVec 32} {len w a : Nat} (ha : Operand a) (na7 : a ≠ 7) :
    RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.inRange a) (fun _ _ => True) := by
  let P := ArithmeticReady base len w
  have save : RelCT isa (fun s t => P s ∧ P t ∧ s.sp = t.sp) (.block VG.Impl.Ffdh.Arm.saveFlag) (fun _ _ => True) :=
    saveFlag_ct.mono (fun _ _ h => h.1.ptr.trans h.2.1.ptr.symm) (fun _ _ h => h)
  have finish : RelCT isa (fun s t => P s ∧ P t ∧ s.sp = t.sp) (.block VG.Impl.Ffdh.Arm.andFlag) (fun _ _ => True) :=
    andFlag_ct.mono (fun _ _ h => h.1.ptr.trans h.2.1.ptr.symm) (fun _ _ h => h)
  have wpGreater (s : State) (h : P s) := WP.mono (greaterOne_ok s h ha.1 ha.2.2 na7 ha) fun _ k => k.1
  have wpSave (s : State) (h : P s) := WP.mono (saveFlag_ok s h) fun _ k => k.1
  unfold VG.Impl.Ffdh.Arm.inRange
  exact relCT_chain (greaterOne_ct ha.1) wpGreater wpGreater
    (relCT_chain save wpSave wpSave (relCT_chain (belowP_ct ha.1)
      (fun s h => belowP_ready s h ha.1) (fun s h => belowP_ready s h ha.1) finish))

end VG.Proof.Ffdh.Arm
