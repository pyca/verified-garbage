module

public import VerifiedGarbage.Proof.Bignum.Arm.R2
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopCT
import VerifiedGarbage.Proof.Bignum.Arm.SquareOpCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.R2Init
import VerifiedGarbage.Proof.Bignum.Arm.R2Constants
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.Arm.R2
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
meta import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopCT
meta import VerifiedGarbage.Proof.Bignum.Arm.SquareOpCT
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Bignum.Arm.R2Init
meta import VerifiedGarbage.Proof.Bignum.Arm.R2Constants
meta import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # RSA R-squared precomputation leaks only public workspace dimensions -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt Operand)

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

/-- The squarings' states, each for its own modulus. -/
def R2SqRel (base : BitVec 32) (len w k : Nat) (s t : State) : Prop :=
  (∃ m, R2Sq base len w m k s) ∧ (∃ m, R2Sq base len w m k t) ∧ s.sp = t.sp

theorem r2Square_ct {base : BitVec 32} {len w k : Nat} :
    RelCT isa (R2SqRel base len w k) (squareOp 4 4) (R2SqRel base len w (2 * k)) := by
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have ct := relCT_keep_sp ((squareOp_ct (base := base) (len := len) (w := w) op4 op4).mono
    (P' := R2SqRel base len w k)
    (fun _ _ h => by
      obtain ⟨⟨m1, h1⟩, ⟨m2, h2⟩, sp⟩ := h
      exact ⟨⟨h1.ready, by rw [h1.modulus]; exact h1.operand⟩,
        ⟨h2.ready, by rw [h2.modulus]; exact h2.operand⟩, sp⟩)
    (fun _ _ _ => trivial)) (fun _ _ h => h.2.2)
  have post (s : State) (h : ∃ m, R2Sq base len w m k s) :
      WP isa (squareOp 4 4) s fun t => ∃ m, R2Sq base len w m (2 * k) t := by
    obtain ⟨m, hm⟩ := h
    exact WP.mono (r2Square_ok s hm) fun t ht => ⟨m, ht.1⟩
  exact (ct.wp (fun s t h => ⟨post s h.1, post t h.2.1⟩)).mono (fun _ _ h => h)
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩)

theorem r2Squares_ct {base : BitVec 32} {len w : Nat} :
    RelCT isa (R2SqRel base len w w) r2Squares (fun _ _ => True) := by
  unfold r2Squares
  exact r2Square_ct.seq (r2Square_ct.seq (r2Square_ct.seq (r2Square_ct.seq (r2Square_ct.seq
    (r2Square_ct.mono (fun _ _ h => h) (fun _ _ _ => trivial))))))

/-- The doublings' states, from one. -/
def R2LoopReady (base : BitVec 32) (len w : Nat) (s : State) : Prop :=
  DoubleLoopReady base len w (65 * w) s ∧ numAt s.mem (State.addr base) w 4 = 1 ∧
    1 < numAt s.mem (State.addr base) w 0

theorem r2_ct {base : BitVec 32} {len w : Nat} (countFits : 128 * w < 2 ^ 32) :
    RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      r2 (fun _ _ => True) := by
  have initPost (s : State) (h : ArithmeticReady base len w s) :
      WP isa r2Init s (R2LoopReady base len w) :=
    WP.mono (r2Init_ok s h) fun _ x => ⟨x.1, x.2.1, by rw [x.2.2.1]; exact h.modulus⟩
  have init := (relCT_keep_sp (r2Init_ct (base := base) (len := len) (w := w))
    (fun _ _ h => h.2.2)).wp (fun s t h => ⟨initPost s h.1, initPost t h.2.1⟩)
  refine init.seq ?_
  have loopPost (s : State) (h : R2LoopReady base len w s) :
      WP isa doubleLoop s fun v => ∃ m, R2Sq base len w m w v :=
    WP.mono (r2Loop_ok s h.1 h.2.1 h.2.2 countFits) fun v x => ⟨_, x.1⟩
  have loop : RelCT isa (fun s t => s.sp = t.sp ∧ R2LoopReady base len w s ∧ R2LoopReady base len w t)
      doubleLoop (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    have hw : 2 ≤ w := h.2.1.1.width ▸ h.2.1.1.layout.1
    exact doubleLoop_ct (by omega) (by omega) s t tr1 tr2 u v ⟨h.2.1.1, h.2.2.1, h.1⟩ e1 e2
  have loopCT := (relCT_keep_sp loop (fun _ _ h => h.1)).wp
    (fun s t h => ⟨loopPost s h.2.1, loopPost t h.2.2⟩)
  exact loopCT.seq (r2Squares_ct.mono (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h))

end VG.Proof.Bignum.Arm
