import VerifiedGarbage.Spec.Camellia

/-!
# Camellia's functions, byte by byte and bit by bit

`byteOf x i` is byte `i` of the 64-bit `x`, from the most significant
(`t(i + 1)` of RFC 3713 §2.4.1). The F-function's byte `i` is the XOR of
the S-boxes of the bytes in row `i` of the P-function (`byteOf_f`); `FL`
and `FLINV` are stated bit by bit (`getLsbD_fl`, `getLsbD_flinv`).
-/

namespace VG.Proof.Camellia

open VG VG.Spec.Camellia

/-- Byte `i` of `x`, from the most significant. -/
def byteOf (x : BitVec 64) (i : Nat) : Byte := (x >>> (56 - 8 * i)).setWidth 8

theorem getLsbD_byteOf (x : BitVec 64) {i j : Nat} (_hi : i < 8) (hj : j < 8) :
    (byteOf x i).getLsbD j = x.getLsbD (56 - 8 * i + j) := by
  simp only [byteOf, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hj, decide_true,
    Bool.true_and]

theorem byteOf_xor (x y : BitVec 64) (i : Nat) : byteOf (x ^^^ y) i = byteOf x i ^^^ byteOf y i := by
  simp only [byteOf, BitVec.ushiftRight_xor_distrib, BitVec.setWidth_xor]

/-- The S-box of byte `i` (from 0): `SBOX1, SBOX2, SBOX3, SBOX4, SBOX2, SBOX3,
SBOX4, SBOX1`. -/
def sboxAt : Nat → Byte → Byte
  | 0 => sbox1 | 1 => sbox2 | 2 => sbox3 | 3 => sbox4
  | 4 => sbox2 | 5 => sbox3 | 6 => sbox4 | _ => sbox1

/-- The bytes (from 0) whose S-boxes byte `i` of the P-function's output XORs. -/
def pRow : Nat → List Nat
  | 0 => [0, 2, 3, 5, 6, 7] | 1 => [0, 1, 3, 4, 6, 7] | 2 => [0, 1, 2, 4, 5, 7]
  | 3 => [1, 2, 3, 4, 5, 6] | 4 => [0, 1, 5, 6, 7] | 5 => [1, 2, 4, 6, 7]
  | 6 => [2, 3, 4, 5, 7] | _ => [0, 3, 4, 5, 6]

/-- The XOR of the bits `j` of `t i` for `i ∈ l`. -/
def xorRow (t : Nat → Byte) (l : List Nat) (j : Nat) : Bool :=
  l.foldr (fun i acc => (t i).getLsbD j ^^ acc) false

set_option linter.unusedSimpArgs false in
/-- Bit `56 - 8 i + j` of eight bytes appended is bit `j` of the `i`-th. -/
theorem getLsbD_cat8 (y0 y1 y2 y3 y4 y5 y6 y7 : Byte) {i j : Nat} (hi : i < 8) (hj : j < 8) :
    (y0 ++ y1 ++ y2 ++ y3 ++ y4 ++ y5 ++ y6 ++ y7).getLsbD (56 - 8 * i + j) =
      ([y0, y1, y2, y3, y4, y5, y6, y7].getD i 0).getLsbD j := by
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [BitVec.getLsbD_append, List.getD_cons_succ, List.getD_cons_zero] <;>
  simp (disch := omega) only [ite_eq_right_of_eq_false, ite_eq_left_of_eq_true, eq_false, eq_true,
    Nat.reduceMul, Nat.reduceSub, ite_true, ite_false] <;>
  congr 1 <;> omega

theorem getLsbD_byteOf_f (x k : BitVec 64) {i j : Nat} (hi : i < 8) (hj : j < 8) :
    (byteOf (f x k) i).getLsbD j =
      xorRow (fun i' => sboxAt i' (byteOf (x ^^^ k) i')) (pRow i) j := by
  have ht : ∀ n, 1 ≤ n → n ≤ 8 →
      ((x ^^^ k) >>> (64 - 8 * n)).setWidth 8 = byteOf (x ^^^ k) (n - 1) := fun n h1 h2 => by
    simp only [byteOf]; congr 2; omega
  -- In one pass: each `rw` would rebuild the whole (large) goal.
  simp only [f, ht 1 (by omega) (by omega), ht 2 (by omega) (by omega), ht 3 (by omega) (by omega),
    ht 4 (by omega) (by omega), ht 5 (by omega) (by omega), ht 6 (by omega) (by omega),
    ht 7 (by omega) (by omega), ht 8 (by omega) (by omega)]
  rw [getLsbD_byteOf _ hi hj, getLsbD_cat8 _ _ _ _ _ _ _ _ hi hj]
  generalize byteOf (x ^^^ k) = b
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [List.getD_cons_succ, List.getD_cons_zero, BitVec.getLsbD_xor, xorRow, pRow, sboxAt,
    List.foldr_cons, List.foldr_nil, Bool.xor_false, Bool.xor_assoc]

/-! ## FL and FLINV, bit by bit

Bit `n` of a 64-bit value; bits `32 … 63` are `x1` (`y1`), `0 … 31` are
`x2` (`y2`), and bit `n` of `x <<< 1` is bit `n - 1` cyclically. -/

theorem getLsbD_fl_lo (x k : BitVec 64) {n : Nat} (hn : n < 32) :
    (fl x k).getLsbD n = (x.getLsbD n ^^ (x.getLsbD (32 + (n + 31) % 32) && k.getLsbD (32 + (n + 31) % 32))) := by
  have hm : (n + 31) % 32 < 32 := Nat.mod_lt _ (by omega)
  simp only [fl, BitVec.getLsbD_append, hn, ite_true, BitVec.getLsbD_xor, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_rotateLeft, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, decide_true, Bool.true_and]
  split
  · rw [show 32 - 1 % 32 + n = (n + 31) % 32 by omega]; simp [hm]
  · rw [show n - 1 % 32 = (n + 31) % 32 by omega]; simp [hm]

theorem getLsbD_fl_hi (x k : BitVec 64) {n : Nat} (hn : 32 ≤ n) (hn' : n < 64) :
    (fl x k).getLsbD n = (x.getLsbD n ^^ ((fl x k).getLsbD (n - 32) || k.getLsbD (n - 32))) := by
  have h1 : ¬ n < 32 := by omega
  have h2 : n - 32 < 32 := by omega
  simp only [fl, BitVec.getLsbD_append, h1, h2, ite_true, ite_false, BitVec.getLsbD_xor, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, decide_true, Bool.true_and]
  rw [show 32 + (n - 32) = n by omega]

theorem getLsbD_flinv_hi (x k : BitVec 64) {n : Nat} (hn : 32 ≤ n) (hn' : n < 64) :
    (flinv x k).getLsbD n = (x.getLsbD n ^^ (x.getLsbD (n - 32) || k.getLsbD (n - 32))) := by
  have h1 : ¬ n < 32 := by omega
  have h2 : n - 32 < 32 := by omega
  simp only [flinv, BitVec.getLsbD_append, h1, h2, ite_false, BitVec.getLsbD_xor, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, decide_true, Bool.true_and]
  rw [show 32 + (n - 32) = n by omega]

theorem getLsbD_flinv_lo (x k : BitVec 64) {n : Nat} (hn : n < 32) :
    (flinv x k).getLsbD n = (x.getLsbD n ^^
      ((flinv x k).getLsbD (32 + (n + 31) % 32) && k.getLsbD (32 + (n + 31) % 32))) := by
  have hm : (n + 31) % 32 < 32 := Nat.mod_lt _ (by omega)
  have h1 : ¬ 32 + (n + 31) % 32 < 32 := by omega
  have h2 : 32 + (n + 31) % 32 - 32 < 32 := by omega
  simp only [flinv, BitVec.getLsbD_append, hn, h1, h2, ite_true, ite_false, BitVec.getLsbD_xor, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_rotateLeft, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, decide_true, Bool.true_and]
  split
  · rw [show 32 - 1 % 32 + n = (n + 31) % 32 by omega]; simp [hm]
  · rw [show n - 1 % 32 = (n + 31) % 32 by omega]; simp [hm]

end VG.Proof.Camellia
