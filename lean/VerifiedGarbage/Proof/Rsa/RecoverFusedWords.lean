module

public import VerifiedGarbage.Proof.Rsa.RecoverFused
import VerifiedGarbage.Proof.Framework.PowLit

/-! # The fused recovery pass, a 32-bit word at a time

`word_eval`: the 32 bits of a word `w`, most significant first, extend the
pass over a prefix `q` of the exponent to `q 2^32 + w`. `bits_succ_last`
takes the bits of a word from its top one, as a shift register holds them:
`wordReg`'s top bit is the next bit, `wordBit`. -/

@[expose] public section

namespace VG.Proof.Rsa.Fused

theorem bits_mod (n b k e : Nat) (s : State) : bits n b k e s = bits n b k (e % 2 ^ k) s := by
  induction k generalizing s e with
  | zero => rfl
  | succ k ih =>
    rw [bits, bits, ih, ih (e := e % 2 ^ (k + 1))]
    have hk : e % 2 ^ (k + 1) % 2 ^ k = e % 2 ^ k :=
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (Nat.le_succ k))
    have hb : e % 2 ^ (k + 1) / 2 ^ k % 2 = e / 2 ^ k % 2 := by
      rw [Nat.pow_succ, Nat.mod_mul, Nat.add_mul_div_left _ _ (Nat.two_pow_pos k),
        Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos k)), Nat.zero_add, Nat.mod_mod]
    rw [hk, hb]

/-- The 32 bits of a word after the prefix `q`. -/
theorem word_eval (n b q w : Nat) (hn : 1 < n) (hw : w < 2 ^ 32) :
    bits n b 32 w (eval n b q) = eval n b (q * 2 ^ 32 + w) := by
  have e := bits_eval n b (q * 2 ^ 32 + w) 32 hn
  rw [show (q * 2 ^ 32 + w) / 2 ^ 32 = q by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 32), Nat.div_eq_of_lt hw, Nat.zero_add],
    bits_mod, show (q * 2 ^ 32 + w) % 2 ^ 32 = w by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hw]] at e
  rw [bits_mod, Nat.mod_eq_of_lt hw]
  exact e

/-- The last bit of a pass is its exponent's low bit. -/
theorem bits_succ_last (n b k e : Nat) (s : State) :
    bits n b (k + 1) e s = step n b (decide (e % 2 = 1)) (bits n b k (e / 2) s) := by
  induction k generalizing s with
  | zero => simp [bits]
  | succ k ih =>
    rw [bits, ih, bits]
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']

/-- A word shifted left `i` times, in 32 bits. -/
abbrev wordReg (w i : Nat) : Nat := w * 2 ^ i % 2 ^ 32

theorem wordReg_succ (w i : Nat) : wordReg w i * 2 % 2 ^ 32 = wordReg w (i + 1) := by
  rw [wordReg, wordReg, Nat.mod_mul_mod, Nat.pow_succ 2 i, Nat.mul_assoc]

/-- The top bit of the register is the bit `31 - i` of the word. -/
theorem wordReg_top {w i : Nat} (hi : i < 32) :
    wordReg w i / 2 ^ 31 = w / 2 ^ (31 - i) % 2 := by
  have e : 2 ^ 32 = 2 * 2 ^ 31 := rfl
  rw [wordReg, e, Nat.mod_mul_left_div_self, show 2 ^ 31 = 2 ^ i * 2 ^ (31 - i) by
    rw [← Nat.pow_add]; congr 1; omega, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ (Nat.two_pow_pos i)]

/-- After `i` bits of the word `w` from `s`, the next one. -/
theorem bits_word {n b w i : Nat} (hi : i < 32) (s : State) :
    bits n b (i + 1) (w / 2 ^ (31 - i)) s =
      step n b (decide (wordReg w i / 2 ^ 31 = 1)) (bits n b i (w / 2 ^ (32 - i)) s) := by
  rw [bits_succ_last, wordReg_top hi, Nat.div_div_eq_div_mul, ← Nat.pow_succ,
    show (31 - i).succ = 32 - i by omega]

end VG.Proof.Rsa.Fused
