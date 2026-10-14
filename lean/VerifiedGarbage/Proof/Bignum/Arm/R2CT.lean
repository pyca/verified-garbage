module

public import VerifiedGarbage.Proof.Bignum.Arm.R2
public import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopCT
meta import VerifiedGarbage.Impl.Bignum.Arm.R2
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # RSA R-squared precomputation leaks only public workspace dimensions -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem r2Constants_ct {base : BitVec 32} {len w : Nat} :
    RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      r2Constants (fun _ _ => True) := by
  have first := relCT_keep_sp
    (smallConst_ct (base := base) (len := len) (w := w) (o := 4) 1
      (by decide) (by decide) (by decide)) (fun _ _ h => h.2.2)
  have wp (s : State) (h : ArithmeticReady base len w s) :
      WP isa (smallConst 4 1) s (ArithmeticReady base len w) :=
    WP.mono (smallConst_ok s 1 h (o := 4) (by decide) (by decide) (by decide) (by decide))
      (fun _ h => h.1)
  have setup := first.wp (fun s t h => ⟨wp s h.1, wp t h.2.1⟩)
  exact (setup.mono (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩)).seq
    (smallConst_ct 2 (o := 7) (by decide) (by decide) (by decide))

theorem r2Init_ct {base : BitVec 32} {len w : Nat} :
    RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      r2Init (fun _ _ => True) := by
  have constants := (r2Constants_ct (base := base) (len := len) (w := w)).wp
    (fun s t h => ⟨WP.mono (r2Constants_ok s h.1) (fun _ h => h.1),
      WP.mono (r2Constants_ok t h.2.1) (fun _ h => h.1)⟩)
  refine constants.seq ?_
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
  intro s t h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact h.2.1.ptr.trans h.2.2.ptr.symm

theorem r2_ct {base : BitVec 32} {len w : Nat} (countFits : 128 * w < 2 ^ 32) :
    RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      r2 (fun _ _ => True) := by
  have init := (relCT_keep_sp (r2Init_ct (base := base) (len := len) (w := w))
    (fun _ _ h => h.2.2)).wp (fun s t h =>
      ⟨WP.mono (r2Init_ok s h.1) (fun _ h => h.1),
        WP.mono (r2Init_ok t h.2.1) (fun _ h => h.1)⟩)
  refine init.seq ?_
  intro s t tr1 tr2 u v h e1 e2
  have hw : 2 ≤ w := h.2.1.width ▸ h.2.1.layout.1
  exact doubleLoop_ct (by omega) countFits s t tr1 tr2 u v ⟨h.2.1, h.2.2, h.1⟩ e1 e2

end VG.Proof.Bignum.Arm
