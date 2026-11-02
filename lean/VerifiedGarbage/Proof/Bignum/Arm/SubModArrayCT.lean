module
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.Bignum.Arm.SubModArray
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady

import VerifiedGarbage.Proof.Bignum.Arm.ClearArrayWideCT
import VerifiedGarbage.Proof.Bignum.Arm.SubModBuffersCT
meta import VerifiedGarbage.Impl.Bignum.Arm.SubModArray
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Bignum.Arm.SubModArrayArgs
import VerifiedGarbage.Proof.Bignum.Arm.ClearArrayWide
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.TaintErase

/-! # Complete array subtraction has no secret-dependent addresses or branches -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt)

theorem subModArray_ct {base : BitVec 32} {len w o a b : Nat}
    (ho : o < 8) (ha : a < 8) (hb : b < 8) (ho0 : o ≠ 0) (fit : 128 ≤ 8 * len) :
    RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      (subModArray o a b) (fun _ _ => True) := by
  let P := ArithmeticReady base len w
  let Q := fun s : State => s.gpr .r0 = base + BitVec.ofNat 32 (arrAt w o) ∧
    s.gpr .r10 = base + BitVec.ofNat 32 (arrAt w a) ∧ s.gpr .r12 = base + BitVec.ofNat 32 (arrAt w b) ∧
    s.gpr .r9 = base + BitVec.ofNat 32 (arrAt w 0) ∧ s.gpr .lr = BitVec.ofNat 32 (2 * w)
  have clear := (relCT_keep_sp (clearArrayWide_ct (base := base) (w := w) ho fit) (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨(clearArrayWide_ok s h.1 ho ho0).mono (fun _ j => j.1),
      (clearArrayWide_ok t h.2.1 ho ho0).mono (fun _ j => j.1)⟩)
  have args : RelCT isa (fun (s t : State) => s.sp = t.sp ∧ P s ∧ P t)
      (subModArrayArgs o a b) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _
      (hc := .seq (Taint.ofRegs [.r0]) (.block []) (.block [])) (by
      rw [← Taint.check_eraseOff _ _ (Taint.noBase_ofRegs [.r0])]
      rfl)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.2.1.ptr.trans h.2.2.ptr.symm
  have argsWP (s : State) (h : P s) : WP isa (subModArrayArgs o a b) s Q := by
    have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
    rw [h.width] at header
    exact (subModArrayArgs_ok s ho ha hb h.workspace fit header h.ptr).mono
      (fun _ j => ⟨j.1, j.2.1, j.2.2.1, j.2.2.2.1, j.2.2.2.2.1⟩)
  have prepared := (relCT_keep_sp args (fun _ _ h => h.1)).wp
    (fun s t h => ⟨argsWP s h.2.1, argsWP t h.2.2⟩)
  have subtract : RelCT isa (fun (s t : State) => s.sp = t.sp ∧ Q s ∧ Q t)
      subModBuffers (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨subModBuffers_ct s t tr1 tr2 u v trivial trivial
      ⟨h.2.1.1.trans h.2.2.1.symm, h.2.1.2.1.trans h.2.2.2.1.symm,
        h.2.1.2.2.1.trans h.2.2.2.2.1.symm, h.2.1.2.2.2.1.trans h.2.2.2.2.2.1.symm,
        h.2.1.2.2.2.2.trans h.2.2.2.2.2.2.symm⟩ e1 e2, trivial⟩
  have final := (relCT_keep_sp subtract (fun _ _ h => h.1)).seq (loadStack_ct .r0 0)
  exact clear.seq (prepared.seq (final.mono (fun _ _ h => h) (fun _ _ _ => trivial)))

end VG.Proof.Bignum.Arm
