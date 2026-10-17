module

public import VerifiedGarbage.Proof.Framework.PowLit

/-!
# RSA with the CRT: the exponent's bits for windows of 5 bits

`expLoop5` (`Impl/Rsa/X86_64/Crt.lean`) reads an exponent of `L` bytes
after `padBits L = 2 L mod 5` zero bits, which make its bits a whole number
of windows (`win5_dvd`). The bits read but not yet in a window are kept at
the top of a word: `b` of them, the low `b` bits of the value `P` of the
bytes read, as `(P mod 2^b) 2^(64 - b)`, and the windows taken so far are
`⌊P / 2^b⌋`. A byte more goes below them (`refill_word`, `refill_val`),
and a window is the word's top 5 bits (`take_hi`, `take_lo`, `take_val`).
These are the facts about it that do not depend on the target.
-/

@[expose] public section

namespace VG.Proof.Bignum

/-- The zero bits before an exponent of `L` bytes: `2 L mod 5`. -/
def padBits (L : Nat) : Nat := 2 * L % 5

theorem padBits_lt (L : Nat) : padBits L < 5 := Nat.mod_lt _ (by decide)

/-- The padded exponent is a whole number of windows. -/
theorem win5_dvd (L : Nat) : (padBits L + 8 * L) % 5 = 0 := by unfold padBits; omega

/-- `⌊L / 5⌋` by a multiplication: the high word of `L M`, for
`M = ⌈2^66 / 5⌉`, shifted right by 2. -/
theorem div5_magic {L : Nat} (h : L < 2 ^ 32) :
    L * 0xCCCCCCCCCCCCCCCD / 2 ^ 64 / 2 ^ 2 = L / 5 := by
  simp only [Nat.reducePow] at *
  omega

/-- The padding from `L mod 5`: `2 (L mod 5)`, less 5 if that is not below
5. -/
theorem padBits_eq (L : Nat) : (if 2 * (L % 5) < 5 then 2 * (L % 5) else 2 * (L % 5) - 5) = padBits L := by
  unfold padBits
  split <;> omega

/-! ## The bits at the top of a word -/

/-- The top 5 of `b ≥ 5` bits at the top of a word. -/
theorem take_hi {r b : Nat} (hb : 5 ≤ b) (hb' : b ≤ 12) (hr : r < 2 ^ b) :
    BitVec.ofNat 64 (r * 2 ^ (64 - b)) >>> 59 = BitVec.ofNat 64 (r / 2 ^ (b - 5)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rcases (by omega : b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 11 ∨ b = 12) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Nat.reducePow, Nat.reduceSub] at * <;> omega

/-- The bits below them, moved up 5. -/
theorem take_lo {r b : Nat} (hb : 5 ≤ b) (hb' : b ≤ 12) (hr : r < 2 ^ b) :
    BitVec.ofNat 64 (r * 2 ^ (64 - b)) <<< 5 = BitVec.ofNat 64 (r % 2 ^ (b - 5) * 2 ^ (64 - (b - 5))) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rcases (by omega : b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 11 ∨ b = 12) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Nat.reducePow, Nat.reduceSub] at * <;> omega

/-- A byte below `b < 5` bits at the top of a word, by a multiplication by
`2^(56 - b)` and an or. -/
theorem refill_word {r b y : Nat} (hb : b < 5) (hr : r < 2 ^ b) (hy : y < 256) :
    BitVec.ofNat 64 y * BitVec.ofNat 64 (2 ^ (56 - b)) ||| BitVec.ofNat 64 (r * 2 ^ (64 - b)) =
      BitVec.ofNat 64 ((256 * r + y) * 2 ^ (56 - b)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  have hp : 2 ^ (64 - b) = 2 ^ 8 * 2 ^ (56 - b) := by rw [← Nat.pow_add]; congr 1; omega
  have h56 : 2 ^ (56 - b) ≤ 2 ^ 56 := Nat.pow_le_pow_right (by decide) (by omega)
  have hb2 : 2 ^ b ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) (by omega)
  have hlo : y * 2 ^ (56 - b) < 2 ^ (64 - b) := by
    rw [hp]; exact Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)
  have h64 : 2 ^ (64 - b) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
  have hlo' : y % 2 ^ 64 * (2 ^ (56 - b) % 2 ^ 64) % 2 ^ 64 = y * 2 ^ (56 - b) := by
    rw [Nat.mod_eq_of_lt (by omega : y < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 2 ^ (56 - b) < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : y * 2 ^ (56 - b) < 2 ^ 64)]
  have hhi : r * 2 ^ (64 - b) < 2 ^ 64 := by
    have := Nat.mul_lt_mul_of_pos_right hr (Nat.two_pow_pos (64 - b))
    rwa [← Nat.pow_add, show b + (64 - b) = 64 by omega] at this
  rw [hlo', Nat.mod_eq_of_lt hhi, Nat.or_comm, Nat.mul_comm r, ← Nat.two_pow_add_eq_or_of_lt hlo]
  have hr1 : 2 ^ (64 - b) * (r + 1) ≤ 2 ^ 64 := by
    have := Nat.mul_le_mul_left (2 ^ (64 - b)) (show r + 1 ≤ 2 ^ b by omega)
    rwa [← Nat.pow_add, show 64 - b + b = 64 by omega] at this
  have key : 2 ^ (64 - b) * r + y * 2 ^ (56 - b) = (256 * r + y) * 2 ^ (56 - b) := by rw [hp]; grind
  rw [← key, Nat.mod_eq_of_lt (by rw [Nat.mul_add, Nat.mul_one] at hr1; omega)]

/-! ## The exponent's value -/

/-- A byte `y` more: `P' = 256 P + y`, with `b + 8` bits left. -/
theorem refill_val {P y b : Nat} (hy : y < 256) :
    (256 * P + y) % 2 ^ (b + 8) = 256 * (P % 2 ^ b) + y ∧ (256 * P + y) / 2 ^ (b + 8) = P / 2 ^ b := by
  have e : 2 ^ (b + 8) = 2 ^ b * 256 := Nat.pow_add 2 b 8
  have hb := Nat.two_pow_pos b
  have hlt : 256 * (P % 2 ^ b) + y < 2 ^ b * 256 := by have := Nat.mod_lt P hb; omega
  have hP : 256 * P + y = 256 * (P % 2 ^ b) + y + 2 ^ b * 256 * (P / 2 ^ b) := by
    have := Nat.div_add_mod P (2 ^ b); grind
  rw [e, hP, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt, Nat.add_mul_div_left _ _ (by omega),
    Nat.div_eq_of_lt hlt, Nat.zero_add]
  exact ⟨rfl, rfl⟩

/-- A window of the top 5 of `b ≥ 5` bits: `32 ⌊P / 2^b⌋ + v`, with
`b - 5` bits left. -/
theorem take_val {P b : Nat} (hb : 5 ≤ b) :
    P / 2 ^ (b - 5) = 32 * (P / 2 ^ b) + P % 2 ^ b / 2 ^ (b - 5) ∧
      P % 2 ^ (b - 5) = P % 2 ^ b % 2 ^ (b - 5) := by
  have e : 2 ^ b = 2 ^ (b - 5) * 32 := by rw [show (32 : Nat) = 2 ^ 5 from rfl, ← Nat.pow_add]; congr 1; omega
  rw [e]
  refine ⟨?_, (Nat.mod_mul_right_mod _ _ _).symm⟩
  rw [Nat.mod_mul_right_div_self, ← Nat.div_div_eq_div_mul]
  have := Nat.div_add_mod (P / 2 ^ (b - 5)) 32
  omega

end VG.Proof.Bignum
