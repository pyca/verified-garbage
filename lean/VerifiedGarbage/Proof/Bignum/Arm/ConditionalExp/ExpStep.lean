module

public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpState
public import VerifiedGarbage.Impl.Bignum.Arm.Square
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Bignum.Arm.SquareOp
import VerifiedGarbage.Proof.Bignum.FoldedPublic
import VerifiedGarbage.Proof.Bignum.Arm.MontOp
import VerifiedGarbage.Proof.Bignum.Math

/-! # Proved squaring, multiplication, and conversion out of Montgomery form -/

@[expose] public section

namespace VG.Proof.Bignum.Arm.ConditionalExp

variable {ok : Prop}
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem exp_square_ok (s : State) {base : BitVec 32} {len w M x E : Nat}
    (h : ExpState ok base len w M x E s) :
    WP isa (squareOp 6 6) s fun t => ExpState ok base len w M x (2 * E) t ∧
      Keeps (State.addr base) len w 6 s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (squareOp_ok s h.ready
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)
    (by rw [h.modulus]; exact h.powerBound)) ?_
  rintro t ⟨ready, modulus, bound, value, keeps, frame, rest⟩
  rw [h.modulus] at modulus bound value
  exact ⟨h.after_y ready modulus keeps bound (fun ho => mont_sq h.coprime (h.powerValue ho) value), keeps, frame, rest⟩

theorem exp_multiply_ok (s : State) {base : BitVec 32} {len w M x E : Nat}
    (h : ExpState ok base len w M x E s) :
    WP isa (montOp 6 6 5) s fun t => ExpState ok base len w M x (E + 1) t ∧
      Keeps (State.addr base) len w 6 s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (montOp_ok s h.ready
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)
    (by rw [h.modulus]; exact h.inputBound)) ?_
  rintro t ⟨ready, modulus, bound, value, keeps, frame, rest⟩
  rw [h.modulus] at modulus bound value
  exact ⟨h.after_y ready modulus keeps bound (fun ho => mont_mulx h.coprime (h.powerValue ho) (h.inputValue ho) value), keeps, frame, rest⟩

theorem exp_finish_ok (s : State) {base : BitVec 32} {len w M x E : Nat}
    (h : ExpState ok base len w M x E s) :
    WP isa (montOp 6 6 7) s fun t => ArithmeticReady base len w t ∧
      (ok → numAt t.mem (State.addr base) w 6 = Spec.Rsa.powMod x E M) ∧
      Keeps (State.addr base) len w 6 s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (montOp_ok s h.ready
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)
    (by rw [h.one]; exact h.ready.modulus)) ?_
  rintro t ⟨ready, _, bound, value, keeps, frame, rest⟩
  rw [h.modulus] at bound value
  rw [h.one] at value
  refine ⟨ready, ?_, keeps, frame, rest⟩
  intro ho
  have final := mont_final_factor h.coprime (h.powerValue ho) value
  rw [Nat.mod_eq_of_lt bound, Nat.mul_one, ← powMod_eq] at final
  exact final

end VG.Proof.Bignum.Arm.ConditionalExp
