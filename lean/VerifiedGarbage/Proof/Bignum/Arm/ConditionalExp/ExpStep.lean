module

public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpState
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Bignum.FoldedPublic
import VerifiedGarbage.Proof.Bignum.Math

/-! # Squaring, multiplication, and conversion out of Montgomery form, by any product

Each by the product of `K` (`TwoExp.Montgomery`), which may need `Q` of the
state and may write the regions `regions`. -/

@[expose] public section

namespace VG.Proof.Bignum.Arm.ConditionalExp

open VG VG.Arm VG.Impl.Bignum.Arm
variable {ok : Prop} {Q : State → Prop} {regions : List Region}
open VG.Proof.Rsa.Mont (numAt Keeps Operand)
open VG.Proof.X25519.Arm (Rest)

theorem operand_5 : Operand 5 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
theorem operand_6 : Operand 6 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
theorem operand_7 : Operand 7 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]

/-- A step within the working space writes within `K`'s regions. -/
theorem liftFrame {base : BitVec 32} {len w : Nat} (K : TwoExp.Montgomery base len w Q regions) {s t : State}
    (f : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem) : Frame regions s.mem t.mem :=
  f.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact K.workspace

theorem exp_square_ok (s : State) {base : BitVec 32} {len w M x E : Nat}
    (K : TwoExp.Montgomery base len w Q regions) (h : ExpState ok base len w M x E s) (q : Q s) :
    WP isa (K.op 6 6 6) s fun t => ExpState ok base len w M x (2 * E) t ∧ Q t ∧
      Keeps (State.addr base) len w 6 s.mem t.mem ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (K.op_ok s 6 6 6 h.ready q operand_6 operand_6 operand_6 (by decide)
    (by rw [h.modulus]; exact h.powerBound)) ?_
  rintro t ⟨ready, modulus, bound, value, keeps, qt, frame, rest⟩
  rw [h.modulus] at modulus bound value
  exact ⟨h.after_y ready modulus keeps bound (fun ho => mont_sq h.coprime (h.powerValue ho) value), qt, keeps,
    frame, rest⟩

theorem exp_multiply_ok (s : State) {base : BitVec 32} {len w M x E : Nat}
    (K : TwoExp.Montgomery base len w Q regions) (h : ExpState ok base len w M x E s) (q : Q s) :
    WP isa (K.op 6 6 5) s fun t => ExpState ok base len w M x (E + 1) t ∧ Q t ∧
      Keeps (State.addr base) len w 6 s.mem t.mem ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (K.op_ok s 6 6 5 h.ready q operand_6 operand_6 operand_5 (by decide)
    (by rw [h.modulus]; exact h.inputBound)) ?_
  rintro t ⟨ready, modulus, bound, value, keeps, qt, frame, rest⟩
  rw [h.modulus] at modulus bound value
  exact ⟨h.after_y ready modulus keeps bound (fun ho => mont_mulx h.coprime (h.powerValue ho) (h.inputValue ho) value),
    qt, keeps, frame, rest⟩

theorem exp_finish_ok (s : State) {base : BitVec 32} {len w M x E : Nat}
    (K : TwoExp.Montgomery base len w Q regions) (h : ExpState ok base len w M x E s) (q : Q s) :
    WP isa (K.op 6 6 7) s fun t => ArithmeticReady base len w t ∧
      (ok → numAt t.mem (State.addr base) w 6 = Spec.Rsa.powMod x E M) ∧ Q t ∧
      Keeps (State.addr base) len w 6 s.mem t.mem ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (K.op_ok s 6 6 7 h.ready q operand_6 operand_6 operand_7 (by decide)
    (by rw [h.one]; exact h.ready.modulus)) ?_
  rintro t ⟨ready, _, bound, value, keeps, qt, frame, rest⟩
  rw [h.modulus] at bound value
  rw [h.one] at value
  refine ⟨ready, ?_, qt, keeps, frame, rest⟩
  intro ho
  have final := mont_final_factor h.coprime (h.powerValue ho) value
  rw [Nat.mod_eq_of_lt bound, Nat.mul_one, ← powMod_eq] at final
  exact final

end VG.Proof.Bignum.Arm.ConditionalExp
