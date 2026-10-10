import VerifiedGarbage.Proof.AesCtr.Counter
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-!
# CTR: the increment, in words

Untrusted: everything here is checked by Lean. The functions implemented in
assembly increment the counter block (`Spec.Ctr.inc`, big-endian) as two
64-bit words or four 32-bit words: each loaded little-endian and
byte-reversed (`rv64`, `rv32`: `bswap` on x86, `rev` on Arm), added to with
a carry, reversed again and stored. `inc_words64` and `inc_words32` state
the blocks they write, given the words' values as numbers, as `Spec.Ctr.inc`
of the block they read.

The general facts are about big-endian numbers in bytes (`toNat`, `ofNat`):
splitting a number across two strings (`ofNat_add`, `toNat_append`), and
adding to a number with a carry into the more significant string
(`ofNat_toNat_append_add`).
-/

namespace VG.Proof.AesCtr

open VG Spec.Ctr
open VG.Spec.Aes (bytesAt)

theorem inc_append (a b : List Byte) (h : a.length + b.length = 16) :
    inc (a ++ b) = ofNat (toNat a + (toNat b + 1) / 256 ^ b.length) a.length ++ ofNat (toNat b + 1) b.length := by
  rw [inc, ← h, ofNat_toNat_append_add]

/-! ## Memory -/

theorem bytesAt_append (m : Mem) (p : Addr) (a b : Nat) :
    bytesAt m p (a + b) = bytesAt m p a ++ bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, BitVec.add_assoc, BitVec.ofNat_add]

/-- Bytes after a store elsewhere. -/
theorem bytesAt_writeW_sep (m : Mem) (P : Addr) {w : Nat} (v : BitVec w) {d n : Nat}
    (hd : w / 8 ≤ d) (hn : d + n < 2 ^ 64) :
    bytesAt (m.writeW P v) (P + BitVec.ofNat 64 d) n = bytesAt m (P + BitVec.ofNat 64 d) n := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i h₁ _
  simp only [bytesAt, List.length_map, List.length_range] at h₁
  simp only [bytesAt, List.getElem_map, List.getElem_range, Mem.writeW]
  apply Mem.write_apply
  rw [Offset.add_add_eq _ rfl, Mem.sub_ofNat_toNat P (by omega)]
  omega

theorem toNat_append_eq {m n : Nat} (x : BitVec m) (y : BitVec n) :
    (x ++ y).toNat = x.toNat * 2 ^ n + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

/-! ## 64-bit words -/

/-- A 64-bit word with its bytes reversed (`bswap` on x86-64, `rev` on
AArch64). -/
def rv64 (a : BitVec 64) : BitVec 64 :=
  a.extractLsb' 0 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8 ++
    a.extractLsb' 32 8 ++ a.extractLsb' 40 8 ++ a.extractLsb' 48 8 ++ a.extractLsb' 56 8

theorem toNat_extract8 {w : Nat} (a : BitVec w) (s : Nat) :
    (a.extractLsb' s 8).toNat = a.toNat / 2 ^ s % 256 := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

/-- The byte at `8 i` of `a`, as a number. -/
theorem toNat_byte {w : Nat} (a : BitVec w) (i : Nat) :
    (a.extractLsb' (8 * i) 8).toNat = a.toNat / 256 ^ i % 256 := by
  rw [toNat_extract8, Nat.pow_mul]

/-- Byte `7 - i` of the reversed word, as a big-endian number, is byte `i`
of the word. -/
theorem rv64_digit (a : BitVec 64) {i : Nat} (hi : i < 8) :
    (rv64 a).toNat / 256 ^ (8 - 1 - i) % 256 = a.toNat / 256 ^ i % 256 := by
  rw [← toNat_byte a i]
  simp only [rv64, toNat_append_eq]
  have h0 := (a.extractLsb' 0 8).isLt
  have h1 := (a.extractLsb' 8 8).isLt
  have h2 := (a.extractLsb' 16 8).isLt
  have h3 := (a.extractLsb' 24 8).isLt
  have h4 := (a.extractLsb' 32 8).isLt
  have h5 := (a.extractLsb' 40 8).isLt
  have h6 := (a.extractLsb' 48 8).isLt
  have h7 := (a.extractLsb' 56 8).isLt
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceMul, Nat.reducePow, Nat.reduceSub] at * <;>
    generalize (a.extractLsb' 0 8).toNat = t0 at * <;>
    generalize (a.extractLsb' 8 8).toNat = t1 at * <;>
    generalize (a.extractLsb' 16 8).toNat = t2 at * <;>
    generalize (a.extractLsb' 24 8).toNat = t3 at * <;>
    generalize (a.extractLsb' 32 8).toNat = t4 at * <;>
    generalize (a.extractLsb' 40 8).toNat = t5 at * <;>
    generalize (a.extractLsb' 48 8).toNat = t6 at * <;>
    generalize (a.extractLsb' 56 8).toNat = t7 at * <;>
    omega

/-- The bytes at `P`, read as the reversed 64-bit word there. -/
theorem bytesAt_rv64 (m : Mem) (P : Addr) : bytesAt m P 8 = ofNat (rv64 (m.readW P 64)).toNat 8 := by
  apply List.ext_getElem (by simp [bytesAt, length_ofNat])
  intro i h₁ _
  simp only [bytesAt, List.length_map, List.length_range] at h₁
  simp only [bytesAt, ofNat, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, rv64_digit _ h₁, ← toNat_byte, Mem.readW, BitVec.setWidth_eq,
    Mem.extractLsb'_read _ _ h₁]

/-- The bytes after storing the reversed word `rv64 v` at `P`: `v`'s, big-endian. -/
theorem bytesAt_writeW_rv64 (m : Mem) (P : Addr) (v : BitVec 64) :
    bytesAt (m.writeW P (rv64 v)) P 8 = ofNat v.toNat 8 := by
  apply List.ext_getElem (by simp [bytesAt, length_ofNat])
  intro i h₁ _
  simp only [bytesAt, List.length_map, List.length_range] at h₁
  simp only [bytesAt, ofNat, List.getElem_map, List.getElem_range]
  have e : (P + BitVec.ofNat 64 i - P).toNat = i := Mem.sub_ofNat_toNat P (by omega)
  simp only [Mem.writeW, Mem.write, e, show i < 64 / 8 by omega, ↓reduceIte]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.setWidth_eq, toNat_byte]
  have := rv64_digit v (i := 7 - i) (by omega)
  rw [show 8 - 1 - (7 - i) = i by omega] at this
  rw [this]

/-- The block at `P` after the increment as two 64-bit words: the
reversed words `rv64 hi` at `P` and `rv64 lo` at `P + 8`, with `lo` the
low word plus 1 and `hi` the high word plus the carry. -/
theorem inc_words64 (m : Mem) (P : Addr) (hi lo : BitVec 64)
    (hlo : lo.toNat = ((rv64 (m.readW (P + BitVec.ofNat 64 8) 64)).toNat + 1) % 2 ^ 64)
    (hhi : hi.toNat = ((rv64 (m.readW P 64)).toNat +
      ((rv64 (m.readW (P + BitVec.ofNat 64 8) 64)).toNat + 1) / 2 ^ 64) % 2 ^ 64) :
    bytesAt ((m.writeW (P + BitVec.ofNat 64 8) (rv64 lo)).writeW P (rv64 hi)) P 16 =
      inc (bytesAt m P 16) := by
  rw [show (16 : Nat) = 8 + 8 from rfl, bytesAt_append, bytesAt_append m, bytesAt_writeW_rv64,
    bytesAt_writeW_sep _ _ _ (by decide) (by decide), bytesAt_writeW_rv64, inc_append _ _ (by simp [bytesAt]),
    bytesAt_rv64 m P, bytesAt_rv64 m (P + BitVec.ofNat 64 8), toNat_ofNat, toNat_ofNat, length_ofNat,
    length_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _), Nat.mod_eq_of_lt (BitVec.isLt _)]
  congr 1
  · exact ofNat_congr (by rw [hhi]; simp only [Nat.reducePow]; omega)
  · exact ofNat_congr (by rw [hlo]; simp only [Nat.reducePow]; omega)

/-! ## 32-bit words -/

/-- A 32-bit word with its bytes reversed (`bswap` on x86, `rev` on ARMv7). -/
def rv32 (a : BitVec 32) : BitVec 32 :=
  a.extractLsb' 0 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8

theorem rv32_digit (a : BitVec 32) {i : Nat} (hi : i < 4) :
    (rv32 a).toNat / 256 ^ (4 - 1 - i) % 256 = a.toNat / 256 ^ i % 256 := by
  rw [← toNat_byte a i]
  simp only [rv32, toNat_append_eq]
  have h0 := (a.extractLsb' 0 8).isLt
  have h1 := (a.extractLsb' 8 8).isLt
  have h2 := (a.extractLsb' 16 8).isLt
  have h3 := (a.extractLsb' 24 8).isLt
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceMul, Nat.reducePow, Nat.reduceSub] at * <;>
    generalize (a.extractLsb' 0 8).toNat = t0 at * <;>
    generalize (a.extractLsb' 8 8).toNat = t1 at * <;>
    generalize (a.extractLsb' 16 8).toNat = t2 at * <;>
    generalize (a.extractLsb' 24 8).toNat = t3 at * <;>
    omega

/-- The bytes at `P`, read as the reversed 32-bit word there. -/
theorem bytesAt_rv32 (m : Mem) (P : Addr) : bytesAt m P 4 = ofNat (rv32 (m.readW P 32)).toNat 4 := by
  apply List.ext_getElem (by simp [bytesAt, length_ofNat])
  intro i h₁ _
  simp only [bytesAt, List.length_map, List.length_range] at h₁
  simp only [bytesAt, ofNat, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, rv32_digit _ h₁, ← toNat_byte, Mem.readW, BitVec.setWidth_eq,
    Mem.extractLsb'_read _ _ h₁]

/-- The bytes after storing the reversed word `rv32 v` at `P`: `v`'s, big-endian. -/
theorem bytesAt_writeW_rv32 (m : Mem) (P : Addr) (v : BitVec 32) :
    bytesAt (m.writeW P (rv32 v)) P 4 = ofNat v.toNat 4 := by
  apply List.ext_getElem (by simp [bytesAt, length_ofNat])
  intro i h₁ _
  simp only [bytesAt, List.length_map, List.length_range] at h₁
  simp only [bytesAt, ofNat, List.getElem_map, List.getElem_range]
  have e : (P + BitVec.ofNat 64 i - P).toNat = i := Mem.sub_ofNat_toNat P (by omega)
  simp only [Mem.writeW, Mem.write, e, show i < 32 / 8 by omega, ↓reduceIte]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.setWidth_eq, toNat_byte]
  have := rv32_digit v (i := 3 - i) (by omega)
  rw [show 4 - 1 - (3 - i) = i by omega] at this
  rw [this]

/-- Bytes after a store at a lower offset. -/
theorem bytesAt_writeW_sep' (m : Mem) (P : Addr) {w : Nat} (v : BitVec w) {a b n : Nat}
    (hd : a + w / 8 ≤ b) (hn : b + n < 2 ^ 64) :
    bytesAt (m.writeW (P + BitVec.ofNat 64 a) v) (P + BitVec.ofNat 64 b) n = bytesAt m (P + BitVec.ofNat 64 b) n := by
  rw [show P + BitVec.ofNat 64 b = (P + BitVec.ofNat 64 a) + BitVec.ofNat 64 (b - a) from
    (Offset.add_add_eq P (by omega)).symm]
  exact bytesAt_writeW_sep _ _ _ (by omega) (by omega)

/-- The carry out of a sum split across two strings. -/
theorem carry_append (a b : List Byte) (x : Nat) :
    (toNat (a ++ b) + x) / 256 ^ (a.length + b.length) = (toNat a + (toNat b + x) / 256 ^ b.length) / 256 ^ a.length := by
  rw [toNat_append, Nat.pow_add, Nat.mul_comm (256 ^ a.length), ← Nat.div_div_eq_div_mul, Nat.add_assoc,
    Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide)), Nat.add_comm]

/-- The block at `P` after the increment as four 32-bit words: the reversed
words `rv32 wᵢ` stored at `P + 12`, `P + 8`, `P + 4` and `P`, each the word
read there plus the carry out of the words after it. -/
theorem inc_words32 (m : Mem) (P : Addr) (w0 w1 w2 w3 : BitVec 32)
    (h3 : w3.toNat = ((rv32 (m.readW (P + BitVec.ofNat 64 12) 32)).toNat + 1) % 2 ^ 32)
    (h2 : w2.toNat = ((rv32 (m.readW (P + BitVec.ofNat 64 8) 32)).toNat +
      ((rv32 (m.readW (P + BitVec.ofNat 64 12) 32)).toNat + 1) / 2 ^ 32) % 2 ^ 32)
    (h1 : w1.toNat = ((rv32 (m.readW (P + BitVec.ofNat 64 4) 32)).toNat +
      ((rv32 (m.readW (P + BitVec.ofNat 64 8) 32)).toNat +
        ((rv32 (m.readW (P + BitVec.ofNat 64 12) 32)).toNat + 1) / 2 ^ 32) / 2 ^ 32) % 2 ^ 32)
    (h0 : w0.toNat = ((rv32 (m.readW P 32)).toNat +
      ((rv32 (m.readW (P + BitVec.ofNat 64 4) 32)).toNat +
        ((rv32 (m.readW (P + BitVec.ofNat 64 8) 32)).toNat +
          ((rv32 (m.readW (P + BitVec.ofNat 64 12) 32)).toNat + 1) / 2 ^ 32) / 2 ^ 32) / 2 ^ 32) % 2 ^ 32) :
    bytesAt ((((m.writeW (P + BitVec.ofNat 64 12) (rv32 w3)).writeW (P + BitVec.ofNat 64 8) (rv32 w2)).writeW
      (P + BitVec.ofNat 64 4) (rv32 w1)).writeW P (rv32 w0)) P 16 = inc (bytesAt m P 16) := by
  have split (m' : Mem) : bytesAt m' P 16 = bytesAt m' P 4 ++ (bytesAt m' (P + BitVec.ofNat 64 4) 4 ++
      (bytesAt m' (P + BitVec.ofNat 64 8) 4 ++ bytesAt m' (P + BitVec.ofNat 64 12) 4)) := by
    rw [show (16 : Nat) = 4 + 12 from rfl, bytesAt_append, show (12 : Nat) = 4 + 8 from rfl, bytesAt_append,
      show (8 : Nat) = 4 + 4 from rfl, bytesAt_append, Offset.add_add_eq P (show 4 + 4 = 8 from rfl),
      Offset.add_add_eq P (show 8 + 4 = 12 from rfl)]
  have l4 (m' : Mem) (Q : Addr) : (bytesAt m' Q 4).length = 4 := by simp [bytesAt]
  rw [split, split m]
  -- The words of the result.
  rw [bytesAt_writeW_rv32, bytesAt_writeW_sep _ _ _ (by decide) (by decide), bytesAt_writeW_rv32,
    bytesAt_writeW_sep _ _ _ (by decide) (by decide), bytesAt_writeW_sep' _ _ _ (by decide) (by decide),
    bytesAt_writeW_rv32, bytesAt_writeW_sep _ _ _ (by decide) (by decide),
    bytesAt_writeW_sep' _ _ _ (by decide) (by decide), bytesAt_writeW_sep' _ _ _ (by decide) (by decide),
    bytesAt_writeW_rv32]
  -- The words of the counter block.
  rw [bytesAt_rv32 m P, bytesAt_rv32 m (P + BitVec.ofNat 64 4), bytesAt_rv32 m (P + BitVec.ofNat 64 8),
    bytesAt_rv32 m (P + BitVec.ofNat 64 12)]
  have b0 := (rv32 (m.readW P 32)).isLt
  have b1 := (rv32 (m.readW (P + BitVec.ofNat 64 4) 32)).isLt
  have b2 := (rv32 (m.readW (P + BitVec.ofNat 64 8) 32)).isLt
  have b3 := (rv32 (m.readW (P + BitVec.ofNat 64 12) 32)).isLt
  generalize (rv32 (m.readW P 32)).toNat = A0 at *
  generalize (rv32 (m.readW (P + BitVec.ofNat 64 4) 32)).toNat = A1 at *
  generalize (rv32 (m.readW (P + BitVec.ofNat 64 8) 32)).toNat = A2 at *
  generalize (rv32 (m.readW (P + BitVec.ofNat 64 12) 32)).toNat = A3 at *
  have hv : toNat (ofNat A0 4 ++ (ofNat A1 4 ++ (ofNat A2 4 ++ ofNat A3 4))) =
      A0 * 2 ^ 96 + A1 * 2 ^ 64 + A2 * 2 ^ 32 + A3 := by
    simp only [toNat_append, toNat_ofNat, length_ofNat, List.length_append, Nat.reducePow, Nat.reduceAdd]
    simp only [Nat.reducePow] at b0 b1 b2 b3
    rw [Nat.mod_eq_of_lt b0, Nat.mod_eq_of_lt b1, Nat.mod_eq_of_lt b2, Nat.mod_eq_of_lt b3]
    omega
  rw [inc, hv, show (16 : Nat) = 4 + (4 + (4 + 4)) from rfl, ofNat_add, ofNat_add, ofNat_add]
  simp only [Nat.reducePow, Nat.reduceAdd] at *
  exact congr (congrArg HAppend.hAppend (ofNat_congr (by omega)))
    (congr (congrArg HAppend.hAppend (ofNat_congr (by omega)))
      (congr (congrArg HAppend.hAppend (ofNat_congr (by omega))) (ofNat_congr (by omega))))

end VG.Proof.AesCtr
