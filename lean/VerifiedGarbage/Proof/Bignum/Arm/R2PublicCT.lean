module

import VerifiedGarbage.Proof.Bignum.Arm.R2Public
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.R2NormalizedConstantsCT
import VerifiedGarbage.Proof.Bignum.Arm.R2NormalizedConstants
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopCT
import VerifiedGarbage.Proof.Bignum.Arm.R2CT
import VerifiedGarbage.Proof.Bignum.Arm.ArrayCompareCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Bignum.Arm.R2Normalized
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Impl.Bignum.Arm.R2Normalized
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
meta import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady

/-! The normalization choice may reveal the public modulus, never a secret input. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)

theorem r2PublicPrepare_ct {base : BitVec 32} {len w : Nat} :
    RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      r2PublicPrepare (fun _ _ => True) := by
  have constants := relCT_keep_sp (r2NormalizedConstants_ct (base := base) (len := len) (w := w))
    (fun _ _ h => h.2.2)
  have post (s : State) (h : ArithmeticReady base len w s) :
      WP isa r2NormalizedConstants s (LayoutFrameReady base len w) :=
    WP.mono (r2NormalizedConstants_ok s h) (fun _ j =>
      ⟨⟨j.1.workspace, j.1.layout, j.1.width, j.1.ptr⟩, j.1.stackRead, j.1.stackSep, j.1.saved⟩)
  have setup := (constants.wp (fun s t h => ⟨post s h.1, post t h.2.1⟩)).mono
    (Q' := fun (s t : State) => LayoutFrameReady base len w s ∧ LayoutFrameReady base len w t ∧ s.sp = t.sp)
    (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩)
  have compare := arrayCompare_ct (base := base) (len := len) (w := w) (a := 4) (b := 0)
    (by decide) (by decide)
  have flag : RelCT isa (fun _ _ => True) (.block [.subs .r11 .r11 (.imm 0)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  exact setup.seq (compare.seq flag)

theorem r2PublicInit_ct {base : BitVec 32} {len w M : Nat} :
    RelCT isa (fun s t =>
      (ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w 0 = M) ∧
      (ArithmeticReady base len w t ∧ numAt t.mem (State.addr base) w 0 = M) ∧ s.sp = t.sp)
      r2PublicInit (fun _ _ => True) := by
  have prepare := relCT_keep_sp ((r2PublicPrepare_ct (base := base) (len := len) (w := w)).mono
    (P' := fun (s t : State) =>
      (ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w 0 = M) ∧
      (ArithmeticReady base len w t ∧ numAt t.mem (State.addr base) w 0 = M) ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)) (fun _ _ h => h.2.2)
  have checked := prepare.wp (fun s t h =>
    ⟨WP.mono (r2PublicPrepare_ok s h.1.1 h.1.2) (fun _ j => j.1),
      WP.mono (r2PublicPrepare_ok t h.2.1.1 h.2.1.2) (fun _ j => j.1)⟩)
  refine checked.seq (RelCT.ite ?_ ?_ ?_)
  · intro s t h
    change some (!s.z) = some (!t.z)
    rw [h.2.1.flag, h.2.2.flag]
  · apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    exact Taint.agree_ofRegs (by simpa using h.1.2.1.ready.ptr.trans h.1.2.2.ready.ptr.symm)
  · apply (r2Init_ct (base := base) (len := len) (w := w)).mono ?_ (fun _ _ h => h)
    intro s t h
    exact ⟨h.1.2.1.ready, h.1.2.2.ready, h.1.1⟩

theorem r2Public_ct {base : BitVec 32} {len w M : Nat} (countFits : 128 * w < 2 ^ 32) :
    RelCT isa (fun s t =>
      (ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w 0 = M) ∧
      (ArithmeticReady base len w t ∧ numAt t.mem (State.addr base) w 0 = M) ∧ s.sp = t.sp)
      r2Public (fun _ _ => True) := by
  let P := R2PublicInitialized base len w M
  have initialized := (relCT_keep_sp (r2PublicInit_ct (base := base) (len := len) (w := w) (M := M))
    (fun _ _ h => h.2.2)).wp (fun s t h =>
      ⟨WP.mono (r2PublicInit_ok s h.1.1 h.1.2) (fun _ j => j.1),
       WP.mono (r2PublicInit_ok t h.2.1.1 h.2.1.2) (fun _ j => j.1)⟩)
  have loop : RelCT isa (fun s t => s.sp = t.sp ∧ P s ∧ P t) doubleLoop (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    have hw : 2 ≤ w := h.2.1.ready.width ▸ h.2.1.ready.layout.1
    exact doubleLoop_ct
      (by unfold r2PublicCount; split <;> omega)
      (by unfold r2PublicCount; split <;> omega)
      s t tr1 tr2 u v ⟨h.2.1.ready, h.2.2.ready, h.1⟩ e1 e2
  have post (s : State) (h : P s) : WP isa doubleLoop s fun t => ∃ m, R2Sq base len w m w t :=
    WP.mono (r2PublicLoop_ok s h countFits) (fun _ j => ⟨M, j.1⟩)
  have powered := ((relCT_keep_sp loop (fun _ _ h => h.1)).wp
    (fun s t h => ⟨post s h.2.1, post t h.2.2⟩)).mono
    (Q' := R2SqRel base len w w) (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩)
  exact initialized.seq (powered.seq r2Squares_ct)

end VG.Proof.Bignum.Arm
