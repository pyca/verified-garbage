import VerifiedGarbage.Proof.GcmSiv.Spec
import VerifiedGarbage.Proof.Siv.Spec

/-!
# AES-GCM-SIV: counter mode a block at a time

Untrusted: everything here is checked by Lean. Byte `p` of `ctr ciph icb x`
is byte `p mod 16` of the keystream block `p / 16` XORed into `x`
(`ctr_getD`). `ctrPart ciph icb x k` is the output with only its first `k`
bytes done: `x` for `k = 0` and `ctr ciph icb x` for `k ≥ len(x)`; changing
the `n ≤ 16` bytes of block `i` in memory to their XOR with the keystream,
and nothing else, does the next `n` (`ctrPart_step`).

The counter blocks: the first is the tag with the top bit of its last byte
set (`initialCounter_words`), and block `j` is the first with its first word
(little-endian) plus `j` (`counterBlock_word`).
-/

namespace VG.Proof.GcmSiv

open VG
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le8 le4 length_le8 length_le4)

theorem ext_getD {a b : List Byte} (hl : a.length = b.length) (h : ∀ p < a.length, a.getD p 0 = b.getD p 0) :
    a = b := by
  apply List.ext_getElem hl
  intro p h₁ h₂
  have := h p h₁
  simpa [List.getD_eq_getElem?_getD, h₁, h₂] using this

/-- The keystream block `i` of counter mode from `icb`. -/
abbrev ksBlock (ciph : Spec.GcmSiv.Cipher) (icb : List Byte) (i : Nat) : List Byte :=
  ciph (Spec.GcmSiv.counterBlock icb i)

theorem length_ctr (ciph : Spec.GcmSiv.Cipher) (hc : ∀ y, (ciph y).length = 16) (icb x : List Byte) :
    (Spec.GcmSiv.ctr ciph icb x).length = x.length := by
  simp only [Spec.GcmSiv.ctr, List.length_zipWith, Siv.length_flatMap16 _ (fun i => hc _)]
  omega

/-- Byte `p` of counter mode's output. -/
theorem ctr_getD (ciph : Spec.GcmSiv.Cipher) (hc : ∀ y, (ciph y).length = 16) (icb x : List Byte) {p : Nat}
    (hp : p < x.length) :
    (Spec.GcmSiv.ctr ciph icb x).getD p 0 = x.getD p 0 ^^^ (ksBlock ciph icb (p / 16)).getD (p % 16) 0 := by
  have hl := Siv.length_flatMap16 (fun i => ciph (Spec.GcmSiv.counterBlock icb i)) (fun i => hc _)
    ((x.length + 15) / 16)
  simp only [Spec.GcmSiv.ctr, List.getD_eq_getElem?_getD, List.getElem?_zipWith,
    List.getElem?_eq_getElem hp, List.getElem?_eq_getElem (show p < _ by rw [hl]; omega)]
  show x[p] ^^^ _ = _
  congr 1
  have h := Siv.getD_flatMap16 (fun i => ciph (Spec.GcmSiv.counterBlock icb i)) (fun i => hc _)
    ((x.length + 15) / 16) (p := p) (by omega)
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show p < _ by rw [hl]; omega),
    Option.getD_some] using h

/-- Counter mode with the first `k` bytes done. -/
def ctrPart (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (k : Nat) : List Byte :=
  (List.range x.length).map fun p =>
    if p < k then x.getD p 0 ^^^ (ksBlock ciph icb (p / 16)).getD (p % 16) 0 else x.getD p 0

theorem length_ctrPart (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (k : Nat) :
    (ctrPart ciph icb x k).length = x.length := by
  simp [ctrPart]

theorem getD_ctrPart (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (k : Nat) {p : Nat} (hp : p < x.length) :
    (ctrPart ciph icb x k).getD p 0 =
      if p < k then x.getD p 0 ^^^ (ksBlock ciph icb (p / 16)).getD (p % 16) 0 else x.getD p 0 := by
  simp [ctrPart, List.getD_eq_getElem?_getD, hp]

theorem ctrPart_zero (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) : ctrPart ciph icb x 0 = x :=
  ext_getD (length_ctrPart _ _ _ _) fun p hp => by
    rw [length_ctrPart] at hp; rw [getD_ctrPart _ _ _ _ hp]; simp

theorem ctrPart_all (ciph : Spec.GcmSiv.Cipher) (hc : ∀ y, (ciph y).length = 16) (icb x : List Byte) {k : Nat}
    (hk : x.length ≤ k) : ctrPart ciph icb x k = Spec.GcmSiv.ctr ciph icb x :=
  ext_getD (by rw [length_ctrPart, length_ctr ciph hc]) fun p hp => by
    rw [length_ctrPart] at hp
    rw [getD_ctrPart _ _ _ _ hp, ite_eq_left (by omega), ctr_getD ciph hc icb x hp]

theorem getD_xor {a b : List Byte} {k : Nat} (ha : k < a.length) (hb : k < b.length) :
    (Spec.Cmac.xor a b).getD k 0 = a.getD k 0 ^^^ b.getD k 0 := by
  simp [Spec.Cmac.xor, List.getD_eq_getElem?_getD, List.getElem?_zipWith, ha, hb]

theorem getD_take {a : List Byte} {n k : Nat} (h : k < n) : (a.take n).getD k 0 = a.getD k 0 := by
  simp [List.getD_eq_getElem?_getD, h]

/-- The `n ≤ 16` bytes of block `i` in memory changed to their XOR with the
keystream, and no other byte of the data. -/
theorem ctrPart_step (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) {m m' : Mem} (P : Addr) {i n : Nat}
    (hn : n ≤ 16)
    (hk : (ksBlock ciph icb i).length = 16)
    (hd : bytesAt m P x.length = ctrPart ciph icb x (16 * i))
    (hf : ∀ p < x.length, (p < 16 * i ∨ 16 * i + n ≤ p) → m' (P + BitVec.ofNat 64 p) = m (P + BitVec.ofNat 64 p))
    (hb : bytesAt m' (P + BitVec.ofNat 64 (16 * i)) n =
      Spec.Cmac.xor (bytesAt m (P + BitVec.ofNat 64 (16 * i)) n) ((ksBlock ciph icb i).take n)) :
    bytesAt m' P x.length = ctrPart ciph icb x (16 * i + n) := by
  have hdk : ∀ p < x.length, m (P + BitVec.ofNat 64 p) = (ctrPart ciph icb x (16 * i)).getD p 0 := fun p hp => by
    rw [← hd, Proof.Cmac.getD_bytesAt _ _ hp]
  refine ext_getD (by rw [Proof.Cmac.bytesAt_length, length_ctrPart]) fun p hp => ?_
  rw [Proof.Cmac.bytesAt_length] at hp
  rw [Proof.Cmac.getD_bytesAt _ _ hp, getD_ctrPart _ _ _ _ hp]
  by_cases h₁ : 16 * i ≤ p ∧ p < 16 * i + n
  · have e : P + BitVec.ofNat 64 p = P + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 (p - 16 * i) := by
      rw [Offset.add_add, show 16 * i + (p - 16 * i) = p by omega]
    have hb' := congrArg (fun l => l.getD (p - 16 * i) 0) hb
    rw [Proof.Cmac.getD_bytesAt _ _ (by omega),
      getD_xor (by rw [Proof.Cmac.bytesAt_length]; omega) (by rw [List.length_take, hk]; omega),
      Proof.Cmac.getD_bytesAt _ _ (by omega), getD_take (by omega)] at hb'
    rw [e, hb', ← e, hdk p hp, getD_ctrPart _ _ _ _ hp, ite_eq_right (by omega), ite_eq_left (by omega),
      show p / 16 = i by omega, show p % 16 = p - 16 * i by omega]
  · rw [hf p hp (by omega), hdk p hp, getD_ctrPart _ _ _ _ hp]
    by_cases h₂ : p < 16 * i
    · rw [ite_eq_left h₂, ite_eq_left (by omega)]
    · rw [ite_eq_right h₂, ite_eq_right (by omega)]

/-! ## The counter blocks -/

/-- The initial counter block of a tag stored as two words. -/
theorem initialCounter_words (a b : BitVec 64) :
    Spec.GcmSiv.initialCounter (le8 a ++ le8 b) = le8 a ++ le8 (b ||| 0x8000000000000000#64) := by
  apply List.ext_getElem (by simp [Spec.GcmSiv.initialCounter, length_le8])
  intro i h₁ h₂
  have hi : i < 16 := by simpa [Spec.GcmSiv.initialCounter] using h₁
  simp only [Spec.GcmSiv.initialCounter, List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD]
  by_cases h : i < 8
  · rw [ite_eq_right (by omega), List.getElem?_append_left (by simp [length_le8]; omega),
      List.getElem_append_left (by simp [length_le8]; omega)]
    simp [le8, h]
  · rw [List.getElem?_append_right (by simp [length_le8]; omega),
      List.getElem_append_right (by simp [length_le8]; omega)]
    simp only [length_le8]
    by_cases h15 : i = 15
    · subst h15
      simp only [↓reduceIte]
      simp [le8]
      ext k hk
      simp [BitVec.getElem_extractLsb']
      have : ∀ k (h : k < 8), (128#8)[k] = (0x8000000000000000#64).getLsbD (56 + k) := by decide
      rw [this k hk]
    · rw [ite_eq_right h15]
      simp [le8, show i - 8 < 8 by omega]
      ext k hk
      simp [BitVec.getElem_extractLsb']
      have : ∀ j < 7, ∀ k < 8, (0x8000000000000000#64).getLsbD (8 * j + k) = false := by decide
      simp [this (i - 8) (by omega) k hk]

theorem leNat_le4 (w : BitVec 32) : Spec.GcmSiv.leNat (le4 w) = w.toNat := by
  have h := w.isLt
  simp only [Spec.GcmSiv.leNat, le4, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil, List.cons_append, List.foldr_cons, List.foldr_nil,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  omega

theorem le4_ofNat (y : Nat) : le4 (BitVec.ofNat 32 y) = Spec.GcmSiv.le32 y := by
  rw [← le4_le32]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  omega

/-- Counter block `j`: the first word of `icb` plus `j`. -/
theorem counterBlock_word (icb : List Byte) (j : Nat) :
    Spec.GcmSiv.counterBlock icb j = le4 (BitVec.ofNat 32 (Spec.GcmSiv.leNat (icb.take 4) + j)) ++ icb.drop 4 := by
  rw [Spec.GcmSiv.counterBlock, le4_ofNat, ← le4_ofNat, ← le4_ofNat]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

/-- A little-endian word in memory. -/
theorem readW32_leNat (m : Mem) (p : Addr) : m.readW p 32 = BitVec.ofNat 32 (Spec.GcmSiv.leNat (bytesAt m p 4)) := by
  rw [← Proof.Cmac.le4_readW, leNat_le4]
  simp

end VG.Proof.GcmSiv
