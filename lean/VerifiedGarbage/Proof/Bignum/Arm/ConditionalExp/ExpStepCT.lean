module
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.Bignum.Arm.Square
public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpState

import VerifiedGarbage.Proof.Bignum.Arm.MontOpCT
import VerifiedGarbage.Proof.Bignum.Arm.SquareOpCT

/-! # Exponentiation arithmetic does not reveal the base or modulus values -/

@[expose] public section

namespace VG.Proof.Bignum.Arm.ConditionalExp

variable {ok : Prop}
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt Operand)

theorem exp_square_ct {base : BitVec 32} {len w M1 M2 x1 x2 E : Nat} :
    RelCT isa (fun s t => ExpState ok base len w M1 x1 E s ∧ ExpState ok base len w M2 x2 E t ∧ s.sp = t.sp)
      (squareOp 6 6) (fun _ _ => True) := by
  apply (squareOp_ct (base := base) (len := len) (w := w) (o := 6) (a := 6)
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])).mono ?_ (fun _ _ h => h)
  intro s t h
  exact ⟨⟨h.1.ready, by rw [h.1.modulus]; exact h.1.powerBound⟩,
    ⟨h.2.1.ready, by rw [h.2.1.modulus]; exact h.2.1.powerBound⟩, h.2.2⟩

theorem exp_multiply_ct {base : BitVec 32} {len w M1 M2 x1 x2 E : Nat}
    (fit : arrAt w 3 + 32 ≤ 8 * len) :
    RelCT isa (fun s t => ExpState ok base len w M1 x1 E s ∧ ExpState ok base len w M2 x2 E t ∧ s.sp = t.sp)
      (montOp 6 6 5) (fun _ _ => True) := by
  apply (montOp_ct (base := base) (o := 6) (a := 6) (b := 5)
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) fit).mono ?_ (fun _ _ h => h)
  intro s t h
  exact ⟨⟨h.1.ready, by rw [h.1.modulus]; exact h.1.inputBound⟩,
    ⟨h.2.1.ready, by rw [h.2.1.modulus]; exact h.2.1.inputBound⟩, h.2.2⟩

theorem exp_finish_ct {base : BitVec 32} {len w M1 M2 x1 x2 E : Nat}
    (fit : arrAt w 3 + 32 ≤ 8 * len) :
    RelCT isa (fun s t => ExpState ok base len w M1 x1 E s ∧ ExpState ok base len w M2 x2 E t ∧ s.sp = t.sp)
      (montOp 6 6 7) (fun _ _ => True) := by
  apply (montOp_ct (base := base) (o := 6) (a := 6) (b := 7)
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) fit).mono ?_ (fun _ _ h => h)
  intro s t h
  exact ⟨⟨h.1.ready, by rw [h.1.one]; exact h.1.ready.modulus⟩,
    ⟨h.2.1.ready, by rw [h.2.1.one]; exact h.2.1.ready.modulus⟩, h.2.2⟩

end VG.Proof.Bignum.Arm.ConditionalExp
