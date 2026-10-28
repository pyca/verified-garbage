module

/-! # Doubled words

RV64I has no rotation. A 32-bit word kept in both halves of a register,
`x * (2³² + 1)` (`dbl x`), is rotated left in the low word by one shift
right (`dbl_rot`), which the SHA-1 rounds use for `ROTL⁵(a)` and
`ROTL³⁰(b)`. A word is doubled by `slli` and `or` from its zero extension
(`dbl_ext`), or by `slli`, `srli` and `or` from any register's low word
(`dbl_mk`). -/

@[expose] public section

namespace VG.RISCV64

/-- A word in both halves of a register. -/
def dbl (x : BitVec 32) : BitVec 64 := x ++ x

theorem dbl_lo (x : BitVec 32) : (dbl x).setWidth 32 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_setWidth, dbl, BitVec.getLsbD_append]; simp [hi]

/-- A doubled word shifted right by `m = 32 - n` is the word rotated left by `n`. -/
theorem dbl_rot (x : BitVec 32) (n m : Nat) (hn : n < 32) (hm : m + n = 32) :
    (dbl x >>> m).setWidth 32 = x.rotateLeft n := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, dbl, BitVec.getLsbD_append,
    BitVec.getLsbD_rotateLeft, Nat.mod_eq_of_lt hn]
  by_cases h : i < n
  · simp only [show m + i < 32 by omega, h, hi, ↓reduceIte, decide_true, Bool.true_and]; congr 1; omega
  · simp only [show ¬ m + i < 32 by omega, h, hi, ↓reduceIte, decide_true, Bool.true_and]; congr 1; omega

/-- A zero-extended word doubled by `slli` and `or`. -/
theorem dbl_ext (x : BitVec 32) : x.setWidth 64 ||| x.setWidth 64 <<< 32 = dbl x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth, dbl,
    BitVec.getLsbD_append]
  by_cases h : i < 32
  · simp [h, hi]
  · simp [hi, h, BitVec.getLsbD_of_ge x i (by omega), show i - 32 < 64 by omega]

/-- A register's low word doubled by `slli`, `srli` and `or`. -/
theorem dbl_mk (v : BitVec 64) : v <<< 32 ||| v <<< 32 >>> 32 = dbl (v.setWidth 32) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft, dbl,
    BitVec.getLsbD_append]
  by_cases h : i < 32
  · simp [h, show 32 + i < 64 by omega]
  · simp [hi, h, show i - 32 < 32 by omega, show ¬ 32 + i < 64 by omega]

end VG.RISCV64
