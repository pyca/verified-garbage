module

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.FoldedPublic
import VerifiedGarbage.Proof.Bignum.Math

/-! # Decode the generator-two result with one shared Montgomery product -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.TwoExp
open VG VG.Arm
open VG.Proof.Rsa.Mont (numAt arrAt Operand)
open VG.Proof.X25519.Arm (Rest)

theorem finish_ok {base : BitVec 32} {len w M E : Nat} {P : State → Prop} {regions : List Region}
    (A : Montgomery base len w P regions) (s : State) (h : Power base len w M E s) (hp : P s) :
    WP isa (A.op 6 6 7) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 6 = Spec.Rsa.powMod 2 E M ∧
      numAt t.mem (State.addr base) w 0 = M ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % M ∧
      numAt t.mem (State.addr base) w 7 = 1 ∧ P t ∧ HeaderKept base s t ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (A.op_ok s 6 6 7 h.ready hp
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)
    (by rw [h.one]; exact h.ready.modulus)) ?_
  rintro t ⟨ready, modulus, bound, value, keeps, pt, frame, rest⟩
  rw [h.modulus] at modulus bound value
  rw [h.one] at value
  have final := mont_final_factor h.coprime h.value value
  rw [Nat.mod_eq_of_lt bound, Nat.mul_one, ← powMod_eq] at final
  have fits : arrAt w 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
  have r2 := (keeps_array_num keeps fits
    (q := 4) (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)).trans h.r2
  have one := (keeps_array_num keeps fits
    (q := 7) (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)).trans h.one
  exact ⟨ready, final, modulus, r2, one, pt, header_of_keeps h.ready keeps, frame, rest⟩

end VG.Proof.Bignum.Arm.TwoExp
