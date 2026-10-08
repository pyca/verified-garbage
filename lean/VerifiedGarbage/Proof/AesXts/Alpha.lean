import VerifiedGarbage.Spec.Xts
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-!
# XTS: multiplication by `α`, in words

Untrusted: everything here is checked by Lean. The functions implemented in
assembly multiply the tweak by `α` (`Spec.Xts.mulAlpha`, §5.2, on bytes, the
first least significant) as little-endian words: each shifted left by one
bit, with the top bit of the word before it shifted in, and the first XORed
with `0x87` if the top bit of the last was set. `mulAlpha_words64` and
`mulAlpha_words32` state the block they write, given the words, as
`mulAlpha` of the block they read; the byte lemmas (`byte_shl`,
`byte_shl_xor`) relate a byte of a shifted word to the bytes of the word.
-/

namespace VG.Proof.AesXts

open VG
open VG.Spec.Aes (bytesAt)
open VG.Spec.Xts (mulAlpha)

theorem shl1_add (b : Byte) (c : Bool) :
    (b <<< 1) + (if c then (1 : Byte) else 0) = (b <<< 1) ||| (if c then (1 : Byte) else 0) := by
  cases c
  · simp
  · apply BitVec.add_eq_or_of_and_eq_zero
    ext i hi
    simp
    omega

theorem mulAlpha_16 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : Byte) :
    mulAlpha [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] =
      [(a0 <<< 1) ^^^ (if a15.msb then 135 else 0),
       (a1 <<< 1) + (if a0.msb then 1 else 0),
       (a2 <<< 1) + (if a1.msb then 1 else 0),
       (a3 <<< 1) + (if a2.msb then 1 else 0),
       (a4 <<< 1) + (if a3.msb then 1 else 0),
       (a5 <<< 1) + (if a4.msb then 1 else 0),
       (a6 <<< 1) + (if a5.msb then 1 else 0),
       (a7 <<< 1) + (if a6.msb then 1 else 0),
       (a8 <<< 1) + (if a7.msb then 1 else 0),
       (a9 <<< 1) + (if a8.msb then 1 else 0),
       (a10 <<< 1) + (if a9.msb then 1 else 0),
       (a11 <<< 1) + (if a10.msb then 1 else 0),
       (a12 <<< 1) + (if a11.msb then 1 else 0),
       (a13 <<< 1) + (if a12.msb then 1 else 0),
       (a14 <<< 1) + (if a13.msb then 1 else 0),
       (a15 <<< 1) + (if a14.msb then 1 else 0)] := by
  simp only [mulAlpha, mulAlpha.step, Bool.false_eq_true, ↓reduceIte]
  cases a15.msb <;> simp

theorem byte_shl {w : Nat} (x : BitVec w) (c : Bool) {j : Nat} (hj : 8 * j + 8 ≤ w) :
    ((x <<< 1) ||| (if c then (1 : BitVec w) else 0)).extractLsb' (8 * j) 8 =
      (x.extractLsb' (8 * j) 8 <<< 1) +
        (if (if j = 0 then c else (x.extractLsb' (8 * (j - 1)) 8).msb) then (1 : Byte) else 0) := by
  rw [shl1_add]
  ext i hi
  simp only [BitVec.getElem_extractLsb', BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.msb_eq_getLsbD_last]
  by_cases h0 : i = 0
  · subst h0
    by_cases hj0 : j = 0
    · subst hj0; cases c <;> simp <;> omega
    · have e : 8 * j - 1 = 8 * (j - 1) + 7 := by omega
      have l : 8 * j < w := by omega
      have z : ¬ 8 * j = 0 := by omega
      have l2 : 8 * (j - 1) + 7 < w := by omega
      by_cases hb : x.getLsbD (8 * (j - 1) + 7) <;> cases c <;>
        simp_all
  · have e : 8 * j + i - 1 = 8 * j + (i - 1) := by omega
    have l : 8 * j + i < w := by omega
    have l3 : 8 * j + (i - 1) < w := by omega
    cases c <;> simp [h0, e, l] <;> split <;> simp [h0, BitVec.getLsbD_eq_getElem l3]

theorem byte_shl_xor {w : Nat} (x : BitVec w) (c : Bool) {j : Nat} (hj : 8 * j + 8 ≤ w) :
    ((x <<< 1) ^^^ (if c then (0x87 : BitVec w) else 0)).extractLsb' (8 * j) 8 =
      if j = 0 then (x.extractLsb' 0 8 <<< 1) ^^^ (if c then (135 : Byte) else 0)
      else (x.extractLsb' (8 * j) 8 <<< 1) + (if (x.extractLsb' (8 * (j - 1)) 8).msb then (1 : Byte) else 0) := by
  have l : 8 * j < w := by omega
  have t : (135#w).toNat = 135 :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by decide : 135 < 2 ^ 8) (Nat.pow_le_pow_right (by decide) (by omega)))
  have k (i : Nat) (h : i < w) : (135#w)[i] = Nat.testBit 135 i := by
    rw [BitVec.getElem_eq_testBit_toNat, t]
  by_cases hj0 : j = 0
  · subst hj0
    simp only [↓reduceIte]
    ext i hi
    have l1 : i < w := by omega
    by_cases h0 : i = 0
    · subst h0; cases c <;> simp [l1, k 0 l1]
    · have l2 : i - 1 < w := by omega
      have k8 : (135#8)[i] = Nat.testBit 135 i := by rw [BitVec.getElem_eq_testBit_toNat]; rfl
      cases c <;> simp [l1, h0, k i l1, k8, BitVec.getLsbD_eq_getElem l2]
  · simp only [hj0, ↓reduceIte]
    have e := byte_shl x false (j := j) hj
    simp only [hj0, ↓reduceIte, Bool.false_eq_true] at e
    rw [← e]
    ext i hi
    have l1 : 8 * j + i < w := by omega
    have k1 : Nat.testBit 135 (8 * j + i) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : 135 < 2 ^ 8) (Nat.pow_le_pow_right (by decide) (by omega)))
    cases c <;> simp [l1, k _ l1, k1]

/-! ## Bytes of words in memory -/

theorem msb_byte {w : Nat} (x : BitVec w) (k : Nat) (hw : w = 8 * k + 8) :
    x.msb = (x.extractLsb' (8 * k) 8).msb := by
  subst hw
  simp only [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_extractLsb']
  simp

theorem bytesAt_append (m : Mem) (p : Addr) (a b : Nat) :
    bytesAt m p (a + b) = bytesAt m p a ++ bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, BitVec.add_assoc, BitVec.ofNat_add]

/-- The bytes of the word at `P`. -/
theorem bytesAt_readW {k : Nat} (m : Mem) (P : Addr) :
    bytesAt m P k = (List.range k).map fun j => (m.readW P (8 * k)).extractLsb' (8 * j) 8 := by
  apply List.map_congr_left
  intro j hj
  rw [Mem.readW, show 8 * k / 8 = k by omega, BitVec.setWidth_eq, Mem.extractLsb'_read _ _ (List.mem_range.mp hj)]

/-- The bytes after storing the word `v` at `P`. -/
theorem bytesAt_writeW {k : Nat} (m : Mem) (P : Addr) (v : BitVec (8 * k)) (hk : k < 2 ^ 64) :
    bytesAt (m.writeW P v) P k = (List.range k).map fun j => v.extractLsb' (8 * j) 8 := by
  apply List.map_congr_left
  intro j hj
  have hj := List.mem_range.mp hj
  have e : (P + BitVec.ofNat 64 j - P).toNat = j := Mem.sub_ofNat_toNat P (by omega)
  simp only [Mem.writeW, Mem.write, e, show j < 8 * k / 8 by omega, ↓reduceIte]
  ext i hi
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_setWidth]
  have l : 8 * j + i < 8 * (8 * k / 8) := by omega
  simp only [l, decide_true, Bool.true_and, BitVec.getLsbD_eq_getElem (show 8 * j + i < 8 * k by omega)]

/-- Bytes below a store. -/
theorem bytesAt_writeW_below (m : Mem) (P : Addr) {w : Nat} (v : BitVec w) {a n : Nat}
    (hd : n ≤ a) (ha : a + w / 8 < 2 ^ 64) :
    bytesAt (m.writeW (P + BitVec.ofNat 64 a) v) P n = bytesAt m P n := by
  apply List.map_congr_left
  intro j hj
  have hj := List.mem_range.mp hj
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [Offset.sub_toNat' P (by omega) (by omega)]
  split <;> omega

/-- Bytes below a store, both at offsets. -/
theorem bytesAt_writeW_below' (m : Mem) (P : Addr) {w : Nat} (v : BitVec w) {d e n : Nat}
    (hd : e + n ≤ d) (ha : d + w / 8 < 2 ^ 64) :
    bytesAt (m.writeW (P + BitVec.ofNat 64 d) v) (P + BitVec.ofNat 64 e) n = bytesAt m (P + BitVec.ofNat 64 e) n := by
  rw [show P + BitVec.ofNat 64 d = (P + BitVec.ofNat 64 e) + BitVec.ofNat 64 (d - e) from
    (Offset.add_add_eq P (by omega)).symm]
  exact bytesAt_writeW_below _ _ _ (by omega) (by omega)

/-- Bytes above a store, both at offsets. -/
theorem bytesAt_writeW_above (m : Mem) (P : Addr) {w : Nat} (v : BitVec w) {d e n : Nat}
    (hd : d + w / 8 ≤ e) (hn : e + n < 2 ^ 64) :
    bytesAt (m.writeW (P + BitVec.ofNat 64 d) v) (P + BitVec.ofNat 64 e) n = bytesAt m (P + BitVec.ofNat 64 e) n := by
  apply List.map_congr_left
  intro j hj
  have hj := List.mem_range.mp hj
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [Offset.add_add_eq P rfl, Offset.sub_toNat' P (by omega) (by omega)]
  split <;> omega

/-! ## The product -/

/-- The tweak at `P` times `α`, as two 64-bit words: the low word shifted
left and XORed with `0x87` if the high word's top bit is set, and the high
word shifted left with the low word's top bit shifted in, stored at `P` and
`P + 8`. -/
theorem mulAlpha_words64 (m : Mem) (P : Addr) :
    bytesAt ((m.writeW P ((m.readW P 64 <<< 1) ^^^
        (if (m.readW (P + BitVec.ofNat 64 8) 64).msb then (0x87 : BitVec 64) else 0))).writeW
      (P + BitVec.ofNat 64 8) ((m.readW (P + BitVec.ofNat 64 8) 64 <<< 1) |||
        (if (m.readW P 64).msb then (1 : BitVec 64) else 0))) P 16 = mulAlpha (bytesAt m P 16) := by
  generalize hL : m.readW P 64 = L
  generalize hH : m.readW (P + BitVec.ofNat 64 8) 64 = H
  rw [show (16 : Nat) = 8 + 8 from rfl, bytesAt_append, bytesAt_append m,
    show P = P + BitVec.ofNat 64 0 by simp,
    bytesAt_writeW_below _ _ _ (by decide) (by decide), ← show P = P + BitVec.ofNat 64 0 by simp,
    bytesAt_writeW (k := 8) _ _ _ (by decide), bytesAt_writeW (k := 8) _ _ _ (by decide),
    bytesAt_readW (k := 8) m P, bytesAt_readW (k := 8) m (P + BitVec.ofNat 64 8), hL, hH]
  simp only [List.range, List.range.loop, List.map, List.cons_append, List.nil_append]
  rw [mulAlpha_16]
  rw [msb_byte H 7 rfl, msb_byte L 7 rfl]
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | rw [byte_shl_xor _ _ (by decide)]; rfl
    | rw [byte_shl _ _ (by decide)]; rfl

/-- The tweak at `P` times `α`, as four 32-bit words `w₀ … w₃`: the first
shifted left and XORed with `0x87` if the last's top bit is set, and each
other shifted left with the top bit of the one before it shifted in, stored
at `P`, `P + 4`, `P + 8` and `P + 12`. -/
theorem mulAlpha_words32 (m : Mem) (P : Addr) :
    let w (d : Nat) := m.readW (P + BitVec.ofNat 64 d) 32
    bytesAt ((((m.writeW P ((w 0 <<< 1) ^^^ (if (w 12).msb then (0x87 : BitVec 32) else 0))).writeW
      (P + BitVec.ofNat 64 4) ((w 4 <<< 1) ||| (if (w 0).msb then (1 : BitVec 32) else 0))).writeW
      (P + BitVec.ofNat 64 8) ((w 8 <<< 1) ||| (if (w 4).msb then (1 : BitVec 32) else 0))).writeW
      (P + BitVec.ofNat 64 12) ((w 12 <<< 1) ||| (if (w 8).msb then (1 : BitVec 32) else 0))) P 16 =
      mulAlpha (bytesAt m P 16) := by
  intro w
  have split (m' : Mem) : bytesAt m' P 16 = bytesAt m' P 4 ++ (bytesAt m' (P + BitVec.ofNat 64 4) 4 ++
      (bytesAt m' (P + BitVec.ofNat 64 8) 4 ++ bytesAt m' (P + BitVec.ofNat 64 12) 4)) := by
    rw [show (16 : Nat) = 4 + 12 from rfl, bytesAt_append, show (12 : Nat) = 4 + 8 from rfl, bytesAt_append,
      show (8 : Nat) = 4 + 4 from rfl, bytesAt_append, Offset.add_add_eq P (show 4 + 4 = 8 from rfl),
      Offset.add_add_eq P (show 8 + 4 = 12 from rfl)]
  rw [split, split m]
  generalize hW0 : (w 0 <<< 1) ^^^ (if (w 12).msb then (0x87 : BitVec 32) else 0) = W0
  generalize hW1 : (w 4 <<< 1) ||| (if (w 0).msb then (1 : BitVec 32) else 0) = W1
  generalize hW2 : (w 8 <<< 1) ||| (if (w 4).msb then (1 : BitVec 32) else 0) = W2
  generalize hW3 : (w 12 <<< 1) ||| (if (w 8).msb then (1 : BitVec 32) else 0) = W3
  -- Each word of the result is the last store to it.
  rw [bytesAt_writeW_below (a := 12) (n := 4) _ _ _ (by decide) (by decide),
    bytesAt_writeW_below (a := 8) (n := 4) _ _ _ (by decide) (by decide),
    bytesAt_writeW_below (a := 4) (n := 4) _ _ _ (by decide) (by decide),
    bytesAt_writeW (k := 4) _ _ _ (by decide),
    bytesAt_writeW_below' (d := 12) (e := 4) (n := 4) _ _ _ (by decide) (by decide),
    bytesAt_writeW_below' (d := 8) (e := 4) (n := 4) _ _ _ (by decide) (by decide),
    bytesAt_writeW (k := 4) _ (P + BitVec.ofNat 64 4) _ (by decide),
    bytesAt_writeW_below' (d := 12) (e := 8) (n := 4) _ _ _ (by decide) (by decide),
    bytesAt_writeW (k := 4) _ (P + BitVec.ofNat 64 8) _ (by decide),
    bytesAt_writeW (k := 4) _ (P + BitVec.ofNat 64 12) _ (by decide)]
  -- The words of the block read.
  rw [bytesAt_readW (k := 4) m P, bytesAt_readW (k := 4) m (P + BitVec.ofNat 64 4),
    bytesAt_readW (k := 4) m (P + BitVec.ofNat 64 8), bytesAt_readW (k := 4) m (P + BitVec.ofNat 64 12),
    ← hW0, ← hW1, ← hW2, ← hW3]
  have r0 : m.readW P 32 = w 0 := by simp [w]
  rw [r0]
  simp only [List.range, List.range.loop, List.map, List.cons_append, List.nil_append]
  rw [mulAlpha_16, msb_byte (w 12) 3 rfl, msb_byte (w 8) 3 rfl, msb_byte (w 4) 3 rfl, msb_byte (w 0) 3 rfl]
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | rw [byte_shl_xor _ _ (by decide)]; rfl
    | rw [byte_shl _ _ (by decide)]; rfl

end VG.Proof.AesXts
