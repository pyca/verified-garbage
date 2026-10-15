module

public import VerifiedGarbage.Proof.Bignum.Arm.ExpStep
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Compute a candidate power without overwriting the squared accumulator -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Spec.Rsa.Mont (numAt arrAt Keeps Operand)
open VG.Proof.X25519.Arm (Rest)

theorem secretMultiply_ok (s : State) {base : BitVec 32} {len w M x E : Nat}
    (h : ExpState base len w M x E s) :
    WP isa (montOp 1 6 5) s fun t => ExpState base len w M x E t ∧
      numAt t.mem (State.addr base) w 1 < M ∧
      numAt t.mem (State.addr base) w 1 % M = x ^ (E + 1) * 2 ^ (64 * w) % M ∧
      Keeps (State.addr base) len w 1 s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (montOp_ok s h.ready
    (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp])
    (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp])
    (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]) (by decide)
    (by rw [h.modulus]; exact h.inputBound)) ?_
  rintro t ⟨ready, modulus, bound, value, keeps, frame, rest⟩
  rw [h.modulus] at modulus bound value
  have fits : arrAt w 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
  have same (q : Nat) (hq : Operand q) (ne : q ≠ 1) := keeps_array_num keeps fits hq ne
  have input := same 5 (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]) (by decide)
  have power := same 6 (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]) (by decide)
  have one := same 7 (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]) (by decide)
  exact ⟨⟨ready, modulus, h.coprime, by rw [input]; exact h.inputBound,
    by rw [input]; exact h.inputValue, by rw [power]; exact h.powerBound,
    by rw [power]; exact h.powerValue, one.trans h.one,
    (same 4 (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]) (by decide)).trans h.r2⟩,
    bound, mont_mulx h.coprime h.powerValue h.inputValue value, keeps, frame, rest⟩

end VG.Proof.Bignum.Arm
