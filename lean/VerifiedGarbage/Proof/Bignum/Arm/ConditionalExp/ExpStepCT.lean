module
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpState
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT

/-! # Exponentiation arithmetic does not reveal the base or modulus values, by any product -/

@[expose] public section

namespace VG.Proof.Bignum.Arm.ConditionalExp

open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt Operand)
variable {ok : Prop} {Q : State → Prop} {regions : List Region}

theorem exp_square_ct {base : BitVec 32} {len w M1 M2 x1 x2 E : Nat} {K : TwoExp.Montgomery base len w Q regions}
    (ct : TwoExp.MontgomeryTiming K) :
    RelCT isa (fun s t => (ExpState ok base len w M1 x1 E s ∧ Q s) ∧ (ExpState ok base len w M2 x2 E t ∧ Q t) ∧
      s.sp = t.sp) (K.op 6 6 6) (fun _ _ => True) := by
  apply (ct.op_ct 6 6 6 (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])).mono ?_ (fun _ _ h => h)
  intro s t h
  exact ⟨⟨h.1.1.ready, h.1.2, by rw [h.1.1.modulus]; exact h.1.1.powerBound⟩,
    ⟨h.2.1.1.ready, h.2.1.2, by rw [h.2.1.1.modulus]; exact h.2.1.1.powerBound⟩, h.2.2⟩

theorem exp_multiply_ct {base : BitVec 32} {len w M1 M2 x1 x2 E : Nat} {K : TwoExp.Montgomery base len w Q regions}
    (ct : TwoExp.MontgomeryTiming K) :
    RelCT isa (fun s t => (ExpState ok base len w M1 x1 E s ∧ Q s) ∧ (ExpState ok base len w M2 x2 E t ∧ Q t) ∧
      s.sp = t.sp) (K.op 6 6 5) (fun _ _ => True) := by
  apply (ct.op_ct 6 6 5 (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])).mono ?_ (fun _ _ h => h)
  intro s t h
  exact ⟨⟨h.1.1.ready, h.1.2, by rw [h.1.1.modulus]; exact h.1.1.inputBound⟩,
    ⟨h.2.1.1.ready, h.2.1.2, by rw [h.2.1.1.modulus]; exact h.2.1.1.inputBound⟩, h.2.2⟩

theorem exp_finish_ct {base : BitVec 32} {len w M1 M2 x1 x2 E : Nat} {K : TwoExp.Montgomery base len w Q regions}
    (ct : TwoExp.MontgomeryTiming K) :
    RelCT isa (fun s t => (ExpState ok base len w M1 x1 E s ∧ Q s) ∧ (ExpState ok base len w M2 x2 E t ∧ Q t) ∧
      s.sp = t.sp) (K.op 6 6 7) (fun _ _ => True) := by
  apply (ct.op_ct 6 6 7 (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])).mono ?_ (fun _ _ h => h)
  intro s t h
  exact ⟨⟨h.1.1.ready, h.1.2, by rw [h.1.1.one]; exact h.1.1.ready.modulus⟩,
    ⟨h.2.1.1.ready, h.2.1.2, by rw [h.2.1.1.one]; exact h.2.1.1.ready.modulus⟩, h.2.2⟩

end VG.Proof.Bignum.Arm.ConditionalExp
