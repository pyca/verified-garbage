module

public import VerifiedGarbage.Proof.Bignum.Arm.MontEncode
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Multiply an ordinary operand by a Montgomery-encoded operand -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Spec.Rsa.Mont (numAt Operand Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem montMixedProduct_ok (s : State) {base : BitVec 32} {len w o a b M x y : Nat}
    (h : ArithmeticReady base len w s) (ho : Operand o) (ha : Operand a) (hb : Operand b) (ho0 : o ≠ 0)
    (modulus : numAt s.mem (State.addr base) w 0 = M) (odd : M % 2 = 1)
    (first : numAt s.mem (State.addr base) w a = x)
    (second : numAt s.mem (State.addr base) w b = y * 2 ^ (64 * w) % M) :
    WP isa (montOp o a b) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 0 = M ∧ numAt t.mem (State.addr base) w o = x * y % M ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have positive : 0 < M := by have := h.modulus; rw [modulus] at this; omega
  refine WP.mono (montOp_ok s h ho ha hb ho0 (by rw [modulus, second]; exact Nat.mod_lt _ positive)) ?_
  rintro t ⟨ready, modT, bound, value, keeps, frame, rest⟩
  rw [modulus] at modT bound value
  rw [first, second, Nat.mul_mod_mod, ← Nat.mul_assoc] at value
  have result := mont_cancel (coprime_pow2 odd (64 * w)) value
  rw [Nat.mod_eq_of_lt bound] at result
  exact ⟨ready, modT, result, keeps, frame, rest⟩

end VG.Proof.Bignum.Arm
