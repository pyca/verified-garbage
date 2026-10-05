import VerifiedGarbage.Proof.Framework.PowLit

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Prune`. -/
section

/-!
# Ed448: pruning a scalar, on 64-bit words

`Spec.Ed448.prune` (clear bits 0–1 and 448–455, set bit 447) on a number given
as seven 64-bit words and a byte: the first word with bits 0–1 cleared, the
seventh with bit 63 set, and no byte above them (`prune_nat`).

This module imports only Lean core: with Mathlib's algebra imported, `2 ^ 448`
can elaborate to a power that unification evaluates, past Lean's threshold
for evaluating exponents.
-/

namespace VG.Proof.Ed448

theorem and_sub4 (x k : Nat) (hk : 2 ≤ k) : x &&& (2 ^ k - 4) = 4 * (x / 4 % 2 ^ (k - 2)) := by
  have e : 2 ^ k - 4 = 2 ^ 2 * (2 ^ (k - 2) - 1) := by
    rw [Nat.mul_sub, Nat.mul_one, ← Nat.pow_add, Nat.add_sub_cancel' hk] <;> rfl
  rw [e, show (4 : Nat) = 2 ^ 2 from rfl]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul, Nat.testBit_mod_two_pow,
    Nat.testBit_two_pow_sub_one, Nat.testBit_div_two_pow]
  by_cases h : 2 ≤ i
  · simp only [h, decide_true, Bool.true_and, Nat.sub_add_cancel h]
    cases x.testBit i <;> simp
  · simp [h]

theorem or_two_pow_mod {q r k : Nat} (hr : r < 2 ^ k) (hq : q ≤ 1) : (2 ^ k * q + r) ||| 2 ^ k = 2 ^ k + r := by
  rw [Nat.two_pow_add_eq_or_of_lt hr]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hq with rfl | rfl
  · rw [Nat.mul_zero, Nat.zero_or, Nat.or_comm]
    simpa using (Nat.two_pow_add_eq_or_of_lt hr 1).symm
  · rw [Nat.mul_one, Nat.or_assoc, Nat.or_comm r, ← Nat.or_assoc, Nat.or_self]
    simpa using (Nat.two_pow_add_eq_or_of_lt hr 1).symm

/-- Setting bit `k` of a number below `2^(k+1)`. -/
theorem or_pow_eq {y k : Nat} (h : y < 2 ^ (k + 1)) : y ||| 2 ^ k = 2 ^ k + y % 2 ^ k := by
  have hq : y / 2 ^ k ≤ 1 := Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)).mpr (by
    rw [Nat.pow_succ] at h; omega))
  have := VG.Proof.Ed448.or_two_pow_mod (q := y / 2 ^ k) (Nat.mod_lt y (Nat.two_pow_pos k)) hq
  rwa [Nat.div_add_mod] at this

/-- `Spec.Ed448.prune` on seven 64-bit words and a byte. -/
theorem prune_nat (w0 w1 w2 w3 w4 w5 w6 b : Nat) (h0 : w0 < 2 ^ 64) (h1 : w1 < 2 ^ 64) (h2 : w2 < 2 ^ 64)
    (h3 : w3 < 2 ^ 64) (h4 : w4 < 2 ^ 64) (h5 : w5 < 2 ^ 64) (h6 : w6 < 2 ^ 64) :
    ((w0 + 2 ^ 64 * (w1 + 2 ^ 64 * (w2 + 2 ^ 64 * (w3 + 2 ^ 64 * (w4 + 2 ^ 64 * (w5 + 2 ^ 64 *
      (w6 + 2 ^ 64 * b))))))) &&& (2 ^ 448 - 4)) ||| 2 ^ 447 =
    (w0 &&& (2 ^ 64 - 4)) + 2 ^ 64 * (w1 + 2 ^ 64 * (w2 + 2 ^ 64 * (w3 + 2 ^ 64 * (w4 + 2 ^ 64 *
      (w5 + 2 ^ 64 * ((w6 ||| 2 ^ 63) + 2 ^ 64 * 0)))))) := by
  rw [VG.Proof.Ed448.and_sub4 _ 448 (by omega), VG.Proof.Ed448.and_sub4 _ 64 (by omega), VG.Proof.Ed448.or_pow_eq (k := 63) (by omega),
    VG.Proof.Ed448.or_pow_eq (k := 447) (by omega)]
  simp only [show 448 - 2 = 446 from rfl, show 64 - 2 = 62 from rfl]
  omega

end VG.Proof.Ed448

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.PruneBytes`. -/
section

/-!
# Ed448: pruning a scalar, on bytes

`Spec.Ed448.prune` (clear bits 0–1 and 448–455, set bit 447) on a number
given as its first byte, the 54 bytes after it (`M`), and its bytes 55 and
56: byte 0 with bits 0–1 cleared, byte 55 with bit 7 set, and byte 56 zero
(`prune_bytes`). Like `Prune.lean`, this module imports only Lean core.
-/

namespace VG.Proof.Ed448

theorem prune_bytes {b0 M b55 b56 : Nat} (h0 : b0 < 256) (hM : M < 2 ^ 432) (h55 : b55 < 256) :
    ((b0 + 256 * (M + 2 ^ 432 * (b55 + 256 * b56))) &&& (2 ^ 448 - 4)) ||| 2 ^ 447 =
      (b0 &&& 252) + 256 * (M + 2 ^ 432 * ((b55 ||| 128) + 256 * 0)) := by
  rw [VG.Proof.Ed448.and_sub4 _ 448 (by omega), show (252 : Nat) = 2 ^ 8 - 4 from rfl, VG.Proof.Ed448.and_sub4 b0 8 (by omega),
    VG.Proof.Ed448.or_pow_eq (k := 447) (by omega), show (128 : Nat) = 2 ^ 7 from rfl, VG.Proof.Ed448.or_pow_eq (k := 7) (by omega)]
  simp only [show 448 - 2 = 446 from rfl, show 8 - 2 = 6 from rfl]
  omega

end VG.Proof.Ed448

end
