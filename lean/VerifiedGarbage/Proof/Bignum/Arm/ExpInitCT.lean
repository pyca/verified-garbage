module
public import VerifiedGarbage.Impl.Bignum.Arm.Exp
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
import VerifiedGarbage.Proof.Bignum.Arm.MontOpCT
import VerifiedGarbage.Proof.Bignum.Arm.MontOp
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.StackCT

/-! # Montgomery exponentiation setup has a public trace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt arrAt Operand)

structure ExpInitReady (base : BitVec 32) (len w : Nat) (s : State) : Prop where
  ready : ArithmeticReady base len w s
  r2bound : numAt s.mem (State.addr base) w 4 < numAt s.mem (State.addr base) w 0

theorem expInit_one_ready (s : State) {base : BitVec 32} {len w : Nat}
    (h : ExpInitReady base len w s) :
    WP isa (smallConst 7 1) s fun t => ExpInitReady base len w t ∧ numAt t.mem (State.addr base) w 7 = 1 := by
  have fits : arrAt w 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
  refine WP.mono (smallConst_ok s (1 : BitVec 32) h.ready (o := 7) (by decide) (by decide) (by decide) (by decide)) ?_
  rintro t ⟨ready, one, _, keeps, _, _⟩
  have r2 := keeps_array_num keeps fits (q := 4) (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)
  have modulus := keeps_array_num keeps fits (q := 0) (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)
  exact ⟨⟨ready, by rw [r2, modulus]; exact h.r2bound⟩, one⟩

theorem expInit_y_ready (s : State) {base : BitVec 32} {len w : Nat}
    (h : ExpInitReady base len w s) (one : numAt s.mem (State.addr base) w 7 = 1) :
    WP isa (montOp 6 4 7) s (ExpInitReady base len w) := by
  have fits : arrAt w 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
  refine WP.mono (montOp_ok s h.ready
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)
    (by rw [one]; exact h.ready.modulus)) ?_
  rintro t ⟨ready, modulus, _, _, keeps, _, _⟩
  have r2 := keeps_array_num keeps fits (q := 4) (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)
  exact ⟨ready, by rw [r2, modulus]; exact h.r2bound⟩

theorem expInit_ct {base : BitVec 32} {len w : Nat} (fit : arrAt w 3 + 32 ≤ 8 * len) :
    RelCT isa (fun s t => ExpInitReady base len w s ∧ ExpInitReady base len w t ∧ s.sp = t.sp)
      expInit (fun _ _ => True) := by
  have init := (relCT_keep_sp ((smallConst_ct (base := base) (len := len) (w := w) (o := 7) 1
    (by decide) (by decide) (by decide)).mono
    (P' := fun (s t : State) => ExpInitReady base len w s ∧ ExpInitReady base len w t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.ready, h.2.1.ready, h.2.2⟩) (fun _ _ h => h)) (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨expInit_one_ready s h.1, expInit_one_ready t h.2.1⟩)
  have op6 : Operand 6 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op7 : Operand 7 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have y := (relCT_keep_sp ((montOp_ct op6 op4 op7 fit).mono
    (P' := fun (s t : State) => s.sp = t.sp ∧
      (ExpInitReady base len w s ∧ numAt s.mem (State.addr base) w 7 = 1) ∧
      (ExpInitReady base len w t ∧ numAt t.mem (State.addr base) w 7 = 1))
    (fun _ _ h => ⟨⟨h.2.1.1.ready, by rw [h.2.1.2]; exact h.2.1.1.ready.modulus⟩,
      ⟨h.2.2.1.ready, by rw [h.2.2.2]; exact h.2.2.1.ready.modulus⟩, h.1⟩) (fun _ _ h => h)) (fun _ _ h => h.1)).wp
    (fun s t h => ⟨expInit_y_ready s h.2.1.1 h.2.1.2, expInit_y_ready t h.2.2.1 h.2.2.2⟩)
  have encoded := (montOp_ct (base := base) (o := 5) (a := 1) (b := 4)
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) op4 fit).mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ ExpInitReady base len w s ∧ ExpInitReady base len w t)
    (fun _ _ h => ⟨⟨h.2.1.ready, h.2.1.r2bound⟩, ⟨h.2.2.ready, h.2.2.r2bound⟩, h.1⟩) (fun _ _ h => h)
  exact init.seq (y.seq encoded)

end VG.Proof.Bignum.Arm
