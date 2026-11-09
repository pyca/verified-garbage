module

public import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Proof.Rsa.Arm.KeyBits
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # A candidate on ARMv7: the bits the code sets and clears

The candidate's two top bits set by or'ing its top word with `0xC0000000`
(`topBits_val`), and its low bit by `orOne` (`candidate_eq`); a witness's
bit 1 set (`or_two_split`) and its top bit cleared by shifting its top word
(`clrTop_val`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime

/-- A word shifted left one bit and back: its top bit cleared. -/
theorem bv_clr_top (v : BitVec 32) : ((v <<< 1) >>> 1).toNat = v.toNat % 2 ^ 31 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have := v.isLt
  rw [show (2 : Nat) ^ 32 = 2 ^ 31 * 2 from rfl, Nat.pow_one, Nat.mul_mod_mul_right,
    Nat.mul_div_cancel _ (by decide)]

/-- The top word, word `i`, of a number of `i + 1` words with its top bit cleared. -/
theorem clrTop_val {x i : Nat} (hx : x < 2 ^ (32 * i + 32)) :
    x % 2 ^ (32 * i) + 2 ^ (32 * i) * ((BitVec.ofNat 32 (x / 2 ^ (32 * i) % 2 ^ 32) <<< 1) >>> 1).toNat +
      2 ^ (32 * (i + 1)) * (x / 2 ^ (32 * (i + 1))) = x % 2 ^ (32 * i + 31) := by
  have e : x / 2 ^ (32 * (i + 1)) = 0 := Nat.div_eq_of_lt (by rwa [Nat.mul_succ])
  rw [e, Nat.mul_zero, Nat.add_zero, bv_clr_top, BitVec.toNat_ofNat, Nat.mod_mod, Nat.mod_mod_of_dvd _ (by decide),
    Nat.pow_add, Nat.mod_mul]

/-- Or'ing with a number below `2^32` changes only the low word. -/
theorem or_low {x b : Nat} (hb : b < 2 ^ 32) : x ||| b = (x % 2 ^ 32 ||| b) + 2 ^ 32 * (x / 2 ^ 32) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hl : x % 2 ^ 32 ||| b < 2 ^ 32 := Nat.or_lt_two_pow (Nat.mod_lt _ (by decide)) hb
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ hl, Nat.testBit_or, Nat.testBit_or, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow]
  by_cases h : i < 32
  · simp [h]
  · simp only [h, ↓reduceIte]
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by omega))),
      Bool.or_false, Nat.sub_add_cancel (by omega)]

end VG.Proof.Dsa.Arm.Prime
