module

import VerifiedGarbage.Proof.Bignum.Arm.SharedR2
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
public import VerifiedGarbage.Proof.Bignum.Arm.R2CT
import VerifiedGarbage.Proof.Bignum.Arm.R2Init
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
public import VerifiedGarbage.Impl.Bignum.Arm.SharedR2
public import VerifiedGarbage.Proof.Bignum.Arm.R2
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery

/-! Shared R-squared setup retains RSA's public-width timing discipline. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.SharedR2
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt Operand)

abbrev SqReady (base : BitVec 32) (len w : Nat) (P : State → Prop) (k : Nat) (s : State) : Prop :=
  (∃ m, R2Sq base len w m k s) ∧ P s

abbrev SqRel (base : BitVec 32) (len w : Nat) (P : State → Prop) (k : Nat) (s t : State) : Prop :=
  SqReady base len w P k s ∧ SqReady base len w P k t ∧ s.sp = t.sp

theorem square_ct {base : BitVec 32} {len w k : Nat} {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len w P regions) (ct : TwoExp.MontgomeryTiming K) :
    RelCT isa (SqRel base len w P k) (K.op 4 4 4) (SqRel base len w P (2 * k)) := by
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op := relCT_keep_sp ((ct.op_ct 4 4 4 op4 op4 op4).mono
    (P' := SqRel base len w P k)
    (fun _ _ h => by
      obtain ⟨⟨⟨m1, h1⟩, p1⟩, ⟨⟨m2, h2⟩, p2⟩, sp⟩ := h
      exact ⟨⟨h1.ready, p1, by rw [h1.modulus]; exact h1.operand⟩,
        ⟨h2.ready, p2, by rw [h2.modulus]; exact h2.operand⟩, sp⟩)
    (fun _ _ h => h)) (fun _ _ h => h.2.2)
  have post (s : State) (h : SqReady base len w P k s) :
      WP isa (K.op 4 4 4) s (SqReady base len w P (2 * k)) := by
    obtain ⟨⟨m, hm⟩, hp⟩ := h
    exact WP.mono (sharedR2Square_ok K s hm hp) fun t ht => ⟨⟨m, ht.1⟩, ht.2.1⟩
  exact (op.wp (fun s t h => ⟨post s h.1, post t h.2.1⟩)).mono (fun _ _ h => h)
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩)

theorem squares_ct {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len w P regions) (ct : TwoExp.MontgomeryTiming K) :
    RelCT isa (SqRel base len w P w) (VG.Impl.Bignum.Arm.SharedR2.squares K.op) (fun _ _ => True) := by
  unfold VG.Impl.Bignum.Arm.SharedR2.squares
  exact (square_ct K ct).seq ((square_ct K ct).seq ((square_ct K ct).seq ((square_ct K ct).seq
    ((square_ct K ct).seq ((square_ct K ct).mono (fun _ _ h => h) (fun _ _ _ => trivial))))))

abbrev LoopReady (base : BitVec 32) (len w : Nat) (P : State → Prop) (s : State) : Prop :=
  R2LoopReady base len w s ∧ P s

theorem r2_ct {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len w P regions) (ct : TwoExp.MontgomeryTiming K)
    (countFits : 128 * w < 2 ^ 32) :
    RelCT isa (fun s t => (ArithmeticReady base len w s ∧ P s) ∧
      (ArithmeticReady base len w t ∧ P t) ∧ s.sp = t.sp)
      (VG.Impl.Bignum.Arm.SharedR2.r2 K.op) (fun _ _ => True) := by
  have initPost (s : State) (h : ArithmeticReady base len w s ∧ P s) :
      WP isa r2Init s (LoopReady base len w P) := by
    refine WP.mono (r2Init_ok s h.1) ?_
    rintro t ⟨ready, one, modulus, frame, rest⟩
    exact ⟨⟨ready, one, by rw [modulus]; exact h.1.modulus⟩, K.stable frame rest h.2⟩
  have init := (relCT_keep_sp ((r2Init_ct (base := base) (len := len) (w := w)).mono
    (P' := fun (s t : State) => (ArithmeticReady base len w s ∧ P s) ∧
      (ArithmeticReady base len w t ∧ P t) ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h))
    (fun _ _ h => h.2.2)).wp (fun s t h => ⟨initPost s h.1, initPost t h.2.1⟩)
  have loopPost (s : State) (h : LoopReady base len w P s) :
      WP isa doubleLoop s (SqReady base len w P w) := by
    refine WP.mono (r2Loop_ok s h.1.1 h.1.2.1 h.1.2.2 countFits) ?_
    rintro t ⟨sq, frame, rest⟩
    exact ⟨⟨_, sq⟩, K.stable frame rest h.2⟩
  have loop : RelCT isa (fun s t => s.sp = t.sp ∧ LoopReady base len w P s ∧ LoopReady base len w P t)
      doubleLoop (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    have hw : 2 ≤ w := h.2.1.1.1.width ▸ h.2.1.1.1.layout.1
    exact doubleLoop_ct (by omega) (by omega) s t tr1 tr2 u v ⟨h.2.1.1.1, h.2.2.1.1, h.1⟩ e1 e2
  have loopCT := (relCT_keep_sp loop (fun _ _ h => h.1)).wp
    (fun s t h => ⟨loopPost s h.2.1, loopPost t h.2.2⟩)
  unfold VG.Impl.Bignum.Arm.SharedR2.r2
  exact init.seq (loopCT.seq ((squares_ct K ct).mono
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h)))

end VG.Proof.Bignum.Arm.SharedR2
