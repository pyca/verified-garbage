module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Bignum.CrtResult
public import VerifiedGarbage.Proof.Bignum.X86.CrtCompute

import VerifiedGarbage.Proof.Bignum.X86.CrtResult
import VerifiedGarbage.Proof.Bignum.WordsPrefix

/-! # An accepted double-width CRT result fits the caller's output length -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.Proof.Mont

theorem narrow_result {m : Mem} {base : Addr} {dst n len N p q dp dq qi x : Nat}
    (value : wordsVal m base dst (2 * n) = resultValue p q dp dq qi x % 2 ^ (128 * n))
    (odd : N % 2 = 1) (pBound : p < N) (qBound : q < N) (product : p * q = N)
    (modulusBound : N < 2 ^ (8 * len)) (length : len ≤ 8 * n) :
    wordsVal m base dst n = VG.Proof.Bignum.crtResult p q dp dq qi x ∧
      wordsVal m base dst n < 2 ^ (8 * len) := by
  obtain ⟨E, B⟩ := accepted_result (dp := dp) (dq := dq) (qi := qi) (x := x) odd pBound qBound product
  have outputBound := Nat.lt_trans B modulusBound
  have wordBound : resultValue p q dp dq qi x < 2 ^ (64 * n) :=
    Nat.lt_of_lt_of_le outputBound (Nat.pow_le_pow_right (by decide) (by omega))
  have wideBound : resultValue p q dp dq qi x < 2 ^ (128 * n) :=
    Nat.lt_of_lt_of_le wordBound (Nat.pow_le_pow_right (by decide) (by omega))
  rw [VG.Proof.Bignum.wordsVal_low_half, value, Nat.mod_eq_of_lt wideBound, Nat.mod_eq_of_lt wordBound]
  exact ⟨E, outputBound⟩

end VG.Proof.Bignum.X86.Crt
