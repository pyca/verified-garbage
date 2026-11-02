module
public import VerifiedGarbage.Impl.Bignum.Arm.MontOp
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady

import VerifiedGarbage.Proof.Bignum.Arm.MontOp
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Impl.Bignum.Arm.R2

/-! # Convert any packed operand into Montgomery representation -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt Operand Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem montEncode_ok (s : State) {base : BitVec 32} {len w o a M : Nat}
    (h : ArithmeticReady base len w s) (ho : Operand o) (ha : Operand a) (ho0 : o ≠ 0)
    (modulus : numAt s.mem (State.addr base) w 0 = M) (odd : M % 2 = 1)
    (r2 : numAt s.mem (State.addr base) w 4 = 2 ^ (128 * w) % M) :
    WP isa (montOp o a 4) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 0 = M ∧
      numAt t.mem (State.addr base) w o = numAt s.mem (State.addr base) w a * 2 ^ (64 * w) % M ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have positive : 0 < M := by have := h.modulus; rw [modulus] at this; omega
  refine WP.mono (montOp_ok s h ho ha
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) ho0
    (by rw [modulus, r2]; exact Nat.mod_lt _ positive)) ?_
  rintro t ⟨ready, modT, bound, value, keeps, frame, rest⟩
  rw [modulus] at modT bound value
  have encoded : numAt t.mem (State.addr base) w o % M = numAt s.mem (State.addr base) w a * 2 ^ (64 * w) % M := by
    apply mont_cancel (coprime_pow2 odd (64 * w))
    rw [value, r2, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod,
      show 128 * w = 64 * w + 64 * w by omega, Nat.pow_add, Nat.mul_assoc]
  rw [Nat.mod_eq_of_lt bound] at encoded
  exact ⟨ready, modT, encoded, keeps, frame, rest⟩

end VG.Proof.Bignum.Arm
