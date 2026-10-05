import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Spec.GcmSiv
import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.Proof.Siv.Spec

/- Proofs formerly in `VerifiedGarbage.Proof.GcmSiv.MulX`. -/
section

/-!
# AES-GCM-SIV: GHASH's product with `x`

Untrusted: everything here is checked by Lean. `mulXG`, the key with which
GHASH computes POLYVAL (`Proof.GcmSiv.Polyval.polyvalFrom_eq`), in a module
of its own, so that code computing it need not import the algebra that
relates the two.
-/

namespace VG.Proof.GcmSiv.Polyval

/-- GHASH's product with `x`: a shift to the right (`Proof.Gcm.Poly.φ_shr1`). -/
def mulXG (h : Spec.Gcm.Block) : Spec.Gcm.Block :=
  if h.getLsbD 0 then (h >>> 1) ^^^ Spec.Gcm.R else h >>> 1

end VG.Proof.GcmSiv.Polyval

end

/- Proofs formerly in `VerifiedGarbage.Proof.GcmSiv.Spec`. -/
section

/-!
# AES-GCM-SIV: lemmas on the specification

Untrusted: everything here is checked by Lean. RFC 8452's cipher on byte
strings is CMAC's (`aesWith_eq`), whose relation to GCM's on blocks, as
`vg_aes_ctr32` computes it, is `Proof.Cmac.aesWith_bytes`; the four bytes of
a counter (`le4_le32`); and the message keys of `derive_keys` as the first
8 bytes of each block, one after the other (`halves`, `deriveKeys_eq`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.GcmSiv

open VG

theorem aesWith_eq (nr : Nat) (w : List Byte) : Spec.GcmSiv.aesWith nr w = Spec.Cmac.aesWith nr w := rfl

theorem aesWith_length (nr : Nat) (w x : List Byte) : (Spec.GcmSiv.aesWith nr w x).length = 16 :=
  Proof.Cmac.aesWith_length nr w x

theorem ctxCiph_length (m : Mem) (K : Addr) (R : Nat) (x : List Byte) :
    (Spec.GcmSiv.ctxCiph m K R x).length = 16 :=
  VG.Proof.GcmSiv.aesWith_length _ _ _

/-- A byte of a number below `2 ^ n` is the byte of the number. -/
theorem byte_mod {x n k : Nat} (h : k + 8 ≤ n) : x % 2 ^ n / 2 ^ k % 2 ^ 8 = x / 2 ^ k % 2 ^ 8 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < 8
  · simp only [hi, decide_true, Bool.true_and, show i + k < n by omega]
  · simp only [hi, decide_false, Bool.false_and]

/-- A number from `k` on: its byte at `k`, then the rest. -/
theorem byte_step (x k : Nat) : x / 2 ^ k % 2 ^ 8 + 256 * (x / 2 ^ (k + 8)) = x / 2 ^ k := by
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul]; exact Nat.mod_add_div _ 256

/-- The four bytes of the counter `i`, as `little_endian_uint32`. -/
theorem le4_le32 (i : Nat) : Proof.Cmac.le4 ((BitVec.ofNat 64 i).setWidth 32) = Spec.GcmSiv.le32 i := by
  apply List.ext_getElem (by simp [Proof.Cmac.le4, Spec.GcmSiv.le32])
  intro j h₁ _
  have hj : j < 4 := by simpa [Proof.Cmac.le4] using h₁
  simp only [Proof.Cmac.le4, Spec.GcmSiv.le32, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 32 ≤ 64)), VG.Proof.GcmSiv.byte_mod (by omega), Nat.pow_mul]

/-- The first 8 bytes of `CIPH(little_endian_uint32(i) ‖ nonce)`, for `i < k`,
one after the other. -/
def halves (ciph : Spec.GcmSiv.Cipher) (nonce : List Byte) (k : Nat) : List Byte :=
  (List.range k).flatMap fun i => (ciph (Spec.GcmSiv.le32 i ++ nonce)).take 8

theorem halves_succ (ciph : Spec.GcmSiv.Cipher) (nonce : List Byte) (k : Nat) :
    VG.Proof.GcmSiv.halves ciph nonce (k + 1) = VG.Proof.GcmSiv.halves ciph nonce k ++ (ciph (Spec.GcmSiv.le32 k ++ nonce)).take 8 := by
  simp [VG.Proof.GcmSiv.halves, List.range_succ, List.flatMap_append]

theorem length_halves {ciph : Spec.GcmSiv.Cipher} (h : ∀ x, (ciph x).length = 16) (nonce : List Byte) (k : Nat) :
    (VG.Proof.GcmSiv.halves ciph nonce k).length = 8 * k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [VG.Proof.GcmSiv.halves_succ, List.length_append, ih, List.length_take, h]; omega

/-- `derive_keys`: the first 16 bytes of the halves, and the rest. -/
theorem deriveKeys_eq {ciph : Spec.GcmSiv.Cipher} (h : ∀ x, (ciph x).length = 16) (keyLen : Nat)
    (nonce : List Byte) :
    Spec.GcmSiv.deriveKeys ciph keyLen nonce =
      ((VG.Proof.GcmSiv.halves ciph nonce (keyLen / 8 + 2)).take 16, (VG.Proof.GcmSiv.halves ciph nonce (keyLen / 8 + 2)).drop 16) := by
  have e : VG.Proof.GcmSiv.halves ciph nonce (keyLen / 8 + 2) =
      ((ciph (Spec.GcmSiv.le32 0 ++ nonce)).take 8 ++ (ciph (Spec.GcmSiv.le32 1 ++ nonce)).take 8) ++
        (List.range (keyLen / 8)).flatMap fun i => (ciph (Spec.GcmSiv.le32 (i + 2) ++ nonce)).take 8 := by
    simp only [VG.Proof.GcmSiv.halves, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.append_assoc]
  have hl : ((ciph (Spec.GcmSiv.le32 0 ++ nonce)).take 8 ++ (ciph (Spec.GcmSiv.le32 1 ++ nonce)).take 8).length =
      16 := by simp [h]
  rw [e, List.take_left' hl, List.drop_left' hl]
  rfl

/-! ## Blocks as two 64-bit words -/

theorem leNat_append (xs ys : List Byte) :
    Spec.GcmSiv.leNat (xs ++ ys) = Spec.GcmSiv.leNat xs + 256 ^ xs.length * Spec.GcmSiv.leNat ys := by
  induction xs with
  | nil => simp [Spec.GcmSiv.leNat]
  | cons x xs ih =>
    simp only [Spec.GcmSiv.leNat, List.cons_append, List.foldr_cons, List.length_cons] at ih ⊢
    rw [ih, Nat.pow_succ, Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 256 (256 ^ xs.length), Nat.add_assoc]

theorem leNat_le8 (a : BitVec 64) : Spec.GcmSiv.leNat (Proof.Cmac.le8 a) = a.toNat := by
  have h := a.isLt
  simp only [Spec.GcmSiv.leNat, Proof.Cmac.le8, List.range_succ, List.range_zero, List.nil_append,
    List.map_append, List.map_cons, List.map_nil, List.cons_append, List.foldr_cons, List.foldr_nil,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  generalize a.toNat = x at h ⊢
  have h7 : x / 2 ^ (8 * 7) % 2 ^ 8 + 256 * 0 = x / 2 ^ (8 * 7) := by
    rw [Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by omega))]
  rw [h7, VG.Proof.GcmSiv.byte_step x (8 * 6), VG.Proof.GcmSiv.byte_step x (8 * 5), VG.Proof.GcmSiv.byte_step x (8 * 4), VG.Proof.GcmSiv.byte_step x (8 * 3),
    VG.Proof.GcmSiv.byte_step x (8 * 2), VG.Proof.GcmSiv.byte_step x (8 * 1), VG.Proof.GcmSiv.byte_step x (8 * 0), Nat.mul_zero, Nat.pow_zero, Nat.div_one]

/-- POLYVAL's field element of a block stored as two little-endian words. -/
theorem ofBytes_le8 (a b : BitVec 64) : Spec.GcmSiv.ofBytes (Proof.Cmac.le8 a ++ Proof.Cmac.le8 b) = b ++ a := by
  apply BitVec.eq_of_toNat_eq
  rw [Spec.GcmSiv.ofBytes, BitVec.toNat_ofNat, VG.Proof.GcmSiv.leNat_append, VG.Proof.GcmSiv.leNat_le8, VG.Proof.GcmSiv.leNat_le8, Proof.Cmac.length_le8,
    BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt a.isLt, Nat.shiftLeft_eq]
  have := a.isLt; have := b.isLt
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- POLYVAL's field element of 16 bytes in memory: two little-endian loads. -/
theorem ofBytes_bytesAt (m : Mem) (p : Addr) :
    Spec.GcmSiv.ofBytes (Spec.Aes.bytesAt m p 16) = m.readW (p + BitVec.ofNat 64 8) 64 ++ m.readW p 64 := by
  rw [Proof.Cmac.bytesAt_split, ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW, VG.Proof.GcmSiv.ofBytes_le8]

/-- The bytes of a field element made of two words. -/
theorem toBytes_append (a b : BitVec 64) : Spec.GcmSiv.toBytes (b ++ a) = Proof.Cmac.le8 a ++ Proof.Cmac.le8 b := by
  apply List.ext_getElem (by simp [Spec.GcmSiv.toBytes, Proof.Cmac.le8])
  intro i h₁ h₂
  have hi : i < 16 := by simpa [Spec.GcmSiv.toBytes] using h₁
  simp only [Spec.GcmSiv.toBytes, List.getElem_map, List.getElem_range]
  by_cases h8 : i < 8
  · rw [List.getElem_append_left (by simpa [Proof.Cmac.le8] using h8)]
    simp only [Proof.Cmac.le8, List.getElem_map, List.getElem_range]
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and, BitVec.getLsbD_append,
      show 8 * i + j < 64 by omega, ↓reduceIte]
  · rw [List.getElem_append_right (by simpa [Proof.Cmac.le8] using h8)]
    simp only [Proof.Cmac.le8, List.getElem_map, List.getElem_range, Proof.Cmac.length_le8]
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and, BitVec.getLsbD_append,
      show ¬ (8 * i + j < 64) by omega, ↓reduceIte]
    congr 1
    simp only [List.length_map, List.length_range]
    omega

/-- `little_endian_uint64(x)`: the bytes of the word `x`. -/
theorem le64_le8 (x : Nat) : Spec.GcmSiv.le64 x = Proof.Cmac.le8 (BitVec.ofNat 64 x) := by
  apply List.ext_getElem (by simp [Proof.Cmac.le8, Spec.GcmSiv.le64])
  intro j h₁ _
  have hj : j < 8 := by simpa [Spec.GcmSiv.le64] using h₁
  simp only [Proof.Cmac.le8, Spec.GcmSiv.le64, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [VG.Proof.GcmSiv.byte_mod (by omega), Nat.pow_mul]

/-! ## POLYVAL's field elements of a string -/

open VG.Spec.GcmSiv (elems ofBytes pad16 zeros)

theorem elems_of_lt {bs : List Byte} (h : bs.length < 16) : elems bs = [] := by
  simp [elems, Nat.div_eq_of_lt h]

theorem elems_cons {bs : List Byte} (h : 16 ≤ bs.length) :
    elems bs = ofBytes (bs.take 16) :: elems (bs.drop 16) := by
  obtain ⟨n, hn⟩ : ∃ n, bs.length / 16 = n + 1 := ⟨bs.length / 16 - 1, by omega⟩
  have hn' : (bs.drop 16).length / 16 = n := by simp only [List.length_drop]; omega
  simp only [elems, hn, hn', List.range_succ_eq_map, List.map_cons, List.map_map]
  refine congrArg _ (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp, List.drop_drop]
  congr 3
  omega

theorem elems_append_aux (ys : List Byte) (n : Nat) :
    ∀ xs : List Byte, xs.length = 16 * n → elems (xs ++ ys) = elems xs ++ elems ys := by
  induction n with
  | zero => intro xs hx; rw [List.eq_nil_of_length_eq_zero hx]; rfl
  | succ n ih =>
    intro xs hx
    rw [VG.Proof.GcmSiv.elems_cons (bs := xs ++ ys) (by simp; omega), VG.Proof.GcmSiv.elems_cons (bs := xs) (by omega),
      List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega),
      ih _ (by simp; omega), List.cons_append]

theorem elems_append {xs ys : List Byte} (hx : xs.length % 16 = 0) : elems (xs ++ ys) = elems xs ++ elems ys :=
  VG.Proof.GcmSiv.elems_append_aux ys (xs.length / 16) xs (by omega)

theorem elems_single {bs : List Byte} (h : bs.length = 16) : elems bs = [ofBytes bs] := by
  rw [VG.Proof.GcmSiv.elems_cons (by omega), List.take_of_length_le (by omega), VG.Proof.GcmSiv.elems_of_lt (by simp; omega)]

/-- The field elements of the `n` blocks at `p`. -/
theorem elems_bytesAt (m : Mem) (p : Addr) (n : Nat) :
    elems (Spec.Aes.bytesAt m p (16 * n)) =
      (List.range n).map fun i => ofBytes (Spec.Aes.bytesAt m (p + BitVec.ofNat 64 (16 * i)) 16) := by
  simp only [elems, Proof.Cmac.bytesAt_length, Nat.mul_div_cancel_left _ (by decide : 0 < 16)]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  congr 1
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt]; omega)
  intro j h₁ h₂
  simp only [Spec.Aes.bytesAt, List.length_map, List.length_range] at h₁
  simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
  rw [BitVec.ofNat_add, BitVec.add_assoc]

theorem length_pad16 (bs : List Byte) : (pad16 bs).length = bs.length + (16 - bs.length % 16) % 16 := by
  simp [pad16, VG.Spec.GcmSiv.zeros]

theorem pad16_mod (bs : List Byte) : (pad16 bs).length % 16 = 0 := by
  rw [VG.Proof.GcmSiv.length_pad16]; omega

/-- A string padded: its whole blocks, then its last bytes padded. -/
theorem pad16_split (bs : List Byte) :
    pad16 bs = bs.take (16 * (bs.length / 16)) ++ pad16 (bs.drop (16 * (bs.length / 16))) := by
  simp only [pad16, List.length_drop, ← List.append_assoc, List.take_append_drop]
  congr 3; omega

/-- The field elements of a padded string. -/
theorem elems_pad16 (bs : List Byte) :
    elems (pad16 bs) = elems (bs.take (16 * (bs.length / 16))) ++
      (if bs.length % 16 = 0 then [] else [ofBytes (bs.drop (16 * (bs.length / 16)) ++ VG.Spec.GcmSiv.zeros (16 - bs.length % 16))]) := by
  rw [VG.Proof.GcmSiv.pad16_split, VG.Proof.GcmSiv.elems_append (by simp; omega)]
  congr 1
  split
  · rename_i h
    rw [List.drop_eq_nil_of_le (by omega)]; rfl
  · rename_i h
    rw [pad16, List.length_drop, VG.Proof.GcmSiv.elems_single (by simp [VG.Spec.GcmSiv.zeros]; omega)]
    congr 3
    have : bs.length - 16 * (bs.length / 16) = bs.length % 16 := by omega
    rw [this, Nat.mod_mod, Nat.mod_eq_of_lt (a := 16 - bs.length % 16) (by omega)]

/-! ## The tag input -/

open VG.Proof.Cmac (le8 le4 length_le8 length_le4)

/-- The tag input of POLYVAL's result `s` (its bytes) and the nonce, as
`tagInput` computes it. -/
def tagOf (s nonce : List Byte) : List Byte :=
  (List.range 16).map fun i =>
    if i < 12 then s.getD i 0 ^^^ nonce.getD i 0
    else if i = 15 then s.getD i 0 &&& 0x7f
    else s.getD i 0

theorem tagInput_eq (authKey nonce pt aad : List Byte) :
    Spec.GcmSiv.tagInput authKey nonce pt aad =
      VG.Proof.GcmSiv.tagOf (Spec.GcmSiv.toBytes (Spec.GcmSiv.polyval (Spec.GcmSiv.ofBytes authKey)
        (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 aad ++ Spec.GcmSiv.pad16 pt ++
          (Spec.GcmSiv.le64 (8 * aad.length) ++ Spec.GcmSiv.le64 (8 * pt.length)))))) nonce := rfl

theorem setWidth_byte_lo (w : BitVec 32) {j : Nat} (hj : j < 4) :
    (w.setWidth 64).extractLsb' (8 * j) 8 = w.extractLsb' (8 * j) 8 := by
  ext k hk
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_setWidth]
  simp; omega

theorem setWidth_byte_hi (w : BitVec 32) {j : Nat} (hj : 4 ≤ j) :
    (w.setWidth 64).extractLsb' (8 * j) 8 = 0 := by
  ext k hk
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_setWidth]
  simp [BitVec.getLsbD_of_ge w (8 * j + k) (by omega)]

theorem mask_bytes : ∀ j < 7, (0x7FFFFFFFFFFFFFFF#64).extractLsb' (8 * j) 8 = BitVec.allOnes 8 := by decide
theorem mask_byte7 : (0x7FFFFFFFFFFFFFFF#64).extractLsb' (8 * 7) 8 = 0x7F#8 := by decide

theorem and_255 (x : BitVec 8) : x &&& 255#8 = x := by
  rw [show (255#8) = BitVec.allOnes 8 from rfl, BitVec.and_allOnes]

theorem tagOf_words (a b n₀ : BitVec 64) (n₁ : BitVec 32) :
    VG.Proof.GcmSiv.tagOf (le8 a ++ le8 b) (le8 n₀ ++ le4 n₁) =
      le8 (a ^^^ n₀) ++ le8 ((b ^^^ n₁.setWidth 64) &&& 0x7FFFFFFFFFFFFFFF#64) := by
  apply List.ext_getElem (by simp [VG.Proof.GcmSiv.tagOf, length_le8])
  intro i h₁ h₂
  have hi : i < 16 := by simpa [VG.Proof.GcmSiv.tagOf] using h₁
  simp only [VG.Proof.GcmSiv.tagOf, List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD]
  rcases (by omega : i < 8 ∨ 8 ≤ i ∧ i < 12 ∨ 12 ≤ i ∧ i < 15 ∨ i = 15) with h | h | h | h
  · simp only [show i < 12 by omega, ↓reduceIte]
    rw [List.getElem?_append_left (by simp [length_le8]; omega),
      List.getElem?_append_left (by simp [length_le8]; omega), List.getElem_append_left (by simp [length_le8]; omega)]
    simp [le8, h, BitVec.extractLsb'_xor]
  · simp only [show i < 12 by omega, ↓reduceIte]
    rw [List.getElem?_append_right (by simp [length_le8]; omega),
      List.getElem?_append_right (by simp [length_le8]; omega), List.getElem_append_right (by simp [length_le8]; omega)]
    simp only [length_le8]
    have hj : i - 8 < 4 := by omega
    simp [le8, le4, hj, BitVec.extractLsb'_xor, BitVec.extractLsb'_and, VG.Proof.GcmSiv.setWidth_byte_lo _ hj,
      VG.Proof.GcmSiv.mask_bytes (i - 8) (by omega), show i - 8 < 8 by omega, VG.Proof.GcmSiv.and_255]
  · simp only [show ¬ i < 12 by omega, show i ≠ 15 by omega, ↓reduceIte]
    rw [List.getElem?_append_right (by simp [length_le8]; omega),
      List.getElem_append_right (by simp [length_le8]; omega)]
    simp only [length_le8]
    simp [le8, BitVec.extractLsb'_xor, BitVec.extractLsb'_and, VG.Proof.GcmSiv.setWidth_byte_hi _ (show 4 ≤ i - 8 by omega),
      VG.Proof.GcmSiv.mask_bytes (i - 8) (by omega), show i - 8 < 8 by omega, VG.Proof.GcmSiv.and_255]
  · subst h
    simp [le8, BitVec.extractLsb'_xor, BitVec.extractLsb'_and, VG.Proof.GcmSiv.setWidth_byte_hi _ (show 4 ≤ 7 by omega)]

end VG.Proof.GcmSiv

/-! ## POLYVAL as GHASH

The statement that POLYVAL with `H` is GHASH with `mulXG H` (`PolyvalEq`,
proved by `Polyval.polyvalFrom_eq`), apart from the algebra of
`Polyval.lean`, so that proofs of implementations can take it as a
hypothesis and need not import that algebra (only `Verified.lean` does).
-/

namespace VG.Proof.GcmSiv.Polyval

/-- RFC 8452 Appendix A: POLYVAL with `H` is GHASH with `H · x`
(`polyvalFrom_eq`). -/
abbrev PolyvalEq : Prop := ∀ (h s : Spec.GcmSiv.Elem) (xs : List Spec.GcmSiv.Elem),
  Spec.GcmSiv.polyvalFrom h s xs = Spec.Gcm.ghashFrom (VG.Proof.GcmSiv.Polyval.mulXG h) s xs

end VG.Proof.GcmSiv.Polyval

end

/- Proofs formerly in `VerifiedGarbage.Proof.GcmSiv.Ctr`. -/
section

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
    (Spec.GcmSiv.ctr ciph icb x).getD p 0 = x.getD p 0 ^^^ (VG.Proof.GcmSiv.ksBlock ciph icb (p / 16)).getD (p % 16) 0 := by
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
    if p < k then x.getD p 0 ^^^ (VG.Proof.GcmSiv.ksBlock ciph icb (p / 16)).getD (p % 16) 0 else x.getD p 0

theorem length_ctrPart (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (k : Nat) :
    (VG.Proof.GcmSiv.ctrPart ciph icb x k).length = x.length := by
  simp [VG.Proof.GcmSiv.ctrPart]

theorem getD_ctrPart (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (k : Nat) {p : Nat} (hp : p < x.length) :
    (VG.Proof.GcmSiv.ctrPart ciph icb x k).getD p 0 =
      if p < k then x.getD p 0 ^^^ (VG.Proof.GcmSiv.ksBlock ciph icb (p / 16)).getD (p % 16) 0 else x.getD p 0 := by
  simp [VG.Proof.GcmSiv.ctrPart, List.getD_eq_getElem?_getD, hp]

theorem ctrPart_zero (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) : VG.Proof.GcmSiv.ctrPart ciph icb x 0 = x :=
  VG.Proof.GcmSiv.ext_getD (VG.Proof.GcmSiv.length_ctrPart _ _ _ _) fun p hp => by
    rw [VG.Proof.GcmSiv.length_ctrPart] at hp; rw [VG.Proof.GcmSiv.getD_ctrPart _ _ _ _ hp]; simp

theorem ctrPart_all (ciph : Spec.GcmSiv.Cipher) (hc : ∀ y, (ciph y).length = 16) (icb x : List Byte) {k : Nat}
    (hk : x.length ≤ k) : VG.Proof.GcmSiv.ctrPart ciph icb x k = Spec.GcmSiv.ctr ciph icb x :=
  VG.Proof.GcmSiv.ext_getD (by rw [VG.Proof.GcmSiv.length_ctrPart, VG.Proof.GcmSiv.length_ctr ciph hc]) fun p hp => by
    rw [VG.Proof.GcmSiv.length_ctrPart] at hp
    rw [VG.Proof.GcmSiv.getD_ctrPart _ _ _ _ hp, ite_eq_left (by omega), VG.Proof.GcmSiv.ctr_getD ciph hc icb x hp]

theorem getD_xor {a b : List Byte} {k : Nat} (ha : k < a.length) (hb : k < b.length) :
    (Spec.Cmac.xor a b).getD k 0 = a.getD k 0 ^^^ b.getD k 0 := by
  simp [Spec.Cmac.xor, List.getD_eq_getElem?_getD, List.getElem?_zipWith, ha, hb]

theorem getD_take {a : List Byte} {n k : Nat} (h : k < n) : (a.take n).getD k 0 = a.getD k 0 := by
  simp [List.getD_eq_getElem?_getD, h]

/-- The `n ≤ 16` bytes of block `i` in memory changed to their XOR with the
keystream, and no other byte of the data. -/
theorem ctrPart_step (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) {m m' : Mem} (P : Addr) {i n : Nat}
    (hn : n ≤ 16)
    (hk : (VG.Proof.GcmSiv.ksBlock ciph icb i).length = 16)
    (hd : bytesAt m P x.length = VG.Proof.GcmSiv.ctrPart ciph icb x (16 * i))
    (hf : ∀ p < x.length, (p < 16 * i ∨ 16 * i + n ≤ p) → m' (P + BitVec.ofNat 64 p) = m (P + BitVec.ofNat 64 p))
    (hb : bytesAt m' (P + BitVec.ofNat 64 (16 * i)) n =
      Spec.Cmac.xor (bytesAt m (P + BitVec.ofNat 64 (16 * i)) n) ((VG.Proof.GcmSiv.ksBlock ciph icb i).take n)) :
    bytesAt m' P x.length = VG.Proof.GcmSiv.ctrPart ciph icb x (16 * i + n) := by
  have hdk : ∀ p < x.length, m (P + BitVec.ofNat 64 p) = (VG.Proof.GcmSiv.ctrPart ciph icb x (16 * i)).getD p 0 := fun p hp => by
    rw [← hd, Proof.Cmac.getD_bytesAt _ _ hp]
  refine VG.Proof.GcmSiv.ext_getD (by rw [Proof.Cmac.bytesAt_length, VG.Proof.GcmSiv.length_ctrPart]) fun p hp => ?_
  rw [Proof.Cmac.bytesAt_length] at hp
  rw [Proof.Cmac.getD_bytesAt _ _ hp, VG.Proof.GcmSiv.getD_ctrPart _ _ _ _ hp]
  by_cases h₁ : 16 * i ≤ p ∧ p < 16 * i + n
  · have e : P + BitVec.ofNat 64 p = P + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 (p - 16 * i) := by
      rw [Offset.add_add, show 16 * i + (p - 16 * i) = p by omega]
    have hb' := congrArg (fun l => l.getD (p - 16 * i) 0) hb
    rw [Proof.Cmac.getD_bytesAt _ _ (by omega),
      VG.Proof.GcmSiv.getD_xor (by rw [Proof.Cmac.bytesAt_length]; omega) (by rw [List.length_take, hk]; omega),
      Proof.Cmac.getD_bytesAt _ _ (by omega), VG.Proof.GcmSiv.getD_take (by omega)] at hb'
    rw [e, hb', ← e, hdk p hp, VG.Proof.GcmSiv.getD_ctrPart _ _ _ _ hp, ite_eq_right (by omega), ite_eq_left (by omega),
      show p / 16 = i by omega, show p % 16 = p - 16 * i by omega]
  · rw [hf p hp (by omega), hdk p hp, VG.Proof.GcmSiv.getD_ctrPart _ _ _ _ hp]
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
  generalize w.toNat = x at h ⊢
  have h3 : x / 2 ^ (8 * 3) % 2 ^ 8 + 256 * 0 = x / 2 ^ (8 * 3) := by
    rw [Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by omega))]
  rw [h3, VG.Proof.GcmSiv.byte_step x (8 * 2), VG.Proof.GcmSiv.byte_step x (8 * 1), VG.Proof.GcmSiv.byte_step x (8 * 0), Nat.mul_zero, Nat.pow_zero,
    Nat.div_one]

theorem le4_ofNat (y : Nat) : le4 (BitVec.ofNat 32 y) = Spec.GcmSiv.le32 y := by
  rw [← VG.Proof.GcmSiv.le4_le32]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  omega

/-- Counter block `j`: the first word of `icb` plus `j`. -/
theorem counterBlock_word (icb : List Byte) (j : Nat) :
    Spec.GcmSiv.counterBlock icb j = le4 (BitVec.ofNat 32 (Spec.GcmSiv.leNat (icb.take 4) + j)) ++ icb.drop 4 := by
  rw [Spec.GcmSiv.counterBlock, VG.Proof.GcmSiv.le4_ofNat, ← VG.Proof.GcmSiv.le4_ofNat, ← VG.Proof.GcmSiv.le4_ofNat]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

/-- A little-endian word in memory. -/
theorem readW32_leNat (m : Mem) (p : Addr) : m.readW p 32 = BitVec.ofNat 32 (Spec.GcmSiv.leNat (bytesAt m p 4)) := by
  rw [← Proof.Cmac.le4_readW, VG.Proof.GcmSiv.leNat_le4]
  simp

end VG.Proof.GcmSiv

end

/- Proofs formerly in `VerifiedGarbage.Proof.GcmSiv.Words`. -/
section

/-!
# AES-GCM-SIV: GHASH's key and the tag input, on 64-bit words

Untrusted: everything here is checked by Lean. Lemmas any target's
implementation of AES-GCM-SIV that computes POLYVAL with GHASH uses, apart
from the algebra of `Proof/GcmSiv/Polyval.lean` (which they need not import):

* `hkeyOf h`, GHASH's product of `h` with `x` (`Polyval.mulXG`, which
  `Polyval.mulXG_eq_hkeyOf` relates to it), on the halves of a block
  (`hkeyOf_words`);
* `tagInputG`, the tag input of RFC 8452 §4 with POLYVAL replaced by GHASH
  with the key `hkeyOf h` (equal to it by `Polyval.tagInput_eq_tagInputG`);
* the top bit of a word cleared by two shifts (`shl_shr_one`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.GcmSiv.Words

open VG

/-- GHASH's product of `h` with `x`: a shift to the right, reduced by `R`
when the bit shifted out is set. -/
def hkeyOf (h : Spec.Gcm.Block) : Spec.Gcm.Block :=
  if h.getLsbD 0 then (h >>> 1) ^^^ Spec.Gcm.R else h >>> 1

theorem and1 (x : BitVec 64) : x &&& 1#64 = if x.getLsbD 0 then 1#64 else 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1#64).toNat = 1 from rfl, Nat.and_one_is_mod]
  cases h : x.getLsbD 0
  · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.toNat_zero]
    simp only [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_zero, Nat.one_and_eq_mod_two] at h
    revert h; cases Nat.mod_two_eq_zero_or_one x.toNat <;> simp_all
  · simp only [↓reduceIte, show (1#64).toNat = 1 from rfl]
    simp only [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_zero, Nat.one_and_eq_mod_two] at h
    revert h; cases Nat.mod_two_eq_zero_or_one x.toNat <;> simp_all

theorem appLo (a b : BitVec 64) {j : Nat} (h : j < 64) : (a ++ b).getLsbD j = b.getLsbD j := by
  rw [BitVec.getLsbD_append]; simp [h]

theorem appHi (a b : BitVec 64) {j : Nat} (h : 64 ≤ j) : (a ++ b).getLsbD j = a.getLsbD (j - 64) := by
  rw [BitVec.getLsbD_append]; simp [show ¬ j < 64 by omega]

/-- `hkeyOf` on the halves of a block, for any words `M` and `C` with the
bits of the carry into the low half and of `R` in the high half. -/
theorem hkeyOf_core (hi lo : BitVec 64) (M C : BitVec 64)
    (hM : ∀ i < 64, M.getLsbD i = (decide (i = 63) && hi.getLsbD 0))
    (hC : ∀ i < 64, C.getLsbD i = (Spec.Gcm.R.getLsbD (i + 64) && lo.getLsbD 0))
    (hR : ∀ i < 64, Spec.Gcm.R.getLsbD i = false) :
    ((hi >>> 1) ^^^ C) ++ ((lo >>> 1) ||| M) = VG.Proof.GcmSiv.Words.hkeyOf (hi ++ lo) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi128
  unfold VG.Proof.GcmSiv.Words.hkeyOf; rw [VG.Proof.GcmSiv.Words.appLo hi lo (by decide)]
  by_cases h64 : i < 64
  · rw [VG.Proof.GcmSiv.Words.appLo _ _ h64, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, hM i h64]
    by_cases h63 : i = 63
    · subst h63
      have e : lo.getLsbD (1 + 63) = false := BitVec.getLsbD_of_ge lo _ (by decide)
      rw [e]
      cases hl : lo.getLsbD 0 <;> simp only [ite_true, ite_false, Bool.false_eq_true, BitVec.getLsbD_xor,
        BitVec.getLsbD_ushiftRight, VG.Proof.GcmSiv.Words.appHi hi lo (show 64 ≤ 1 + 63 by decide), hR 63 (by decide)] <;> simp
    · have e : (hi ++ lo).getLsbD (1 + i) = lo.getLsbD (1 + i) := VG.Proof.GcmSiv.Words.appLo hi lo (by omega)
      cases hl : lo.getLsbD 0 <;> simp only [ite_true, ite_false, Bool.false_eq_true, BitVec.getLsbD_xor,
        BitVec.getLsbD_ushiftRight, e, hR i h64, decide_eq_false h63] <;> simp
  · rw [VG.Proof.GcmSiv.Words.appHi _ _ (by omega), BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight, hC (i - 64) (by omega),
      show i - 64 + 64 = i by omega]
    have e : (hi ++ lo).getLsbD (1 + i) = hi.getLsbD (1 + (i - 64)) := by
      rw [VG.Proof.GcmSiv.Words.appHi hi lo (by omega)]; congr 1; omega
    cases hl : lo.getLsbD 0 <;> simp only [ite_true, ite_false, Bool.false_eq_true, BitVec.getLsbD_xor,
      BitVec.getLsbD_ushiftRight, e] <;> simp

/-- GHASH's product with `x`, as a sequence of 64-bit operations computes it
on the halves of a block. -/
theorem hkeyOf_words (hi lo : BitVec 64) :
    ((hi >>> 1) ^^^ (0xE100000000000000#64 &&& (0#64 - (lo &&& 1#64)))) ++
      ((lo >>> 1) ||| (hi &&& 1#64).rotateRight 1) = VG.Proof.GcmSiv.Words.hkeyOf (hi ++ lo) := by
  have hR : ∀ i < 64, Spec.Gcm.R.getLsbD i = false := by decide +kernel
  have hR' : ∀ i < 64, (0xE100000000000000#64 : BitVec 64).getLsbD i = Spec.Gcm.R.getLsbD (i + 64) := by
    decide +kernel
  have h1 : ∀ i < 64, (0x8000000000000000#64 : BitVec 64).getLsbD i = decide (i = 63) := by decide +kernel
  refine VG.Proof.GcmSiv.Words.hkeyOf_core hi lo _ _ (fun i hi64 => ?_) (fun i hi64 => ?_) hR
  · rw [VG.Proof.GcmSiv.Words.and1 hi]; cases h : hi.getLsbD 0 <;> simp [h1 i hi64]
  · rw [VG.Proof.GcmSiv.Words.and1 lo]; cases h : lo.getLsbD 0 <;> simp [hR' i hi64]

/-- The top bit of a word cleared by shifting it out and back. -/
theorem shl_shr_one (x : BitVec 64) : (x <<< 1) >>> 1 = x &&& 0x7FFFFFFFFFFFFFFF#64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hm : ∀ i < 64, (0x7FFFFFFFFFFFFFFF#64 : BitVec 64).getLsbD i = decide (i < 63) := by decide +kernel
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, hm i hi, BitVec.getLsbD_shiftLeft]
  by_cases h : i < 63
  · simp only [show 1 + i < 64 by omega, decide_true, Bool.true_and, show ¬ (1 + i < 1) by omega,
      decide_false, Bool.not_false, h, Bool.and_true]
    congr 1; omega
  · simp only [show ¬ (1 + i < 64) by omega, decide_false, Bool.false_and, h, Bool.and_false]

/-- The tag input of RFC 8452 §4 (`Spec.GcmSiv.tagInput`), with POLYVAL
computed as GHASH with the key `hkeyOf` of the authentication key. -/
def tagInputG (authKey nonce pt aad : List Byte) : List Byte :=
  VG.Proof.GcmSiv.tagOf (Spec.GcmSiv.toBytes (Spec.Gcm.ghashFrom (VG.Proof.GcmSiv.Words.hkeyOf (Spec.GcmSiv.ofBytes authKey)) 0
    (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 aad ++ Spec.GcmSiv.pad16 pt ++
      (Spec.GcmSiv.le64 (8 * aad.length) ++ Spec.GcmSiv.le64 (8 * pt.length)))))) nonce

end VG.Proof.GcmSiv.Words

end

/- Proofs formerly in `VerifiedGarbage.Proof.GcmSiv.Words32`. -/
section

/-!
# AES-GCM-SIV: blocks as 32-bit words

Untrusted: everything here is checked by Lean. The counterparts, on the
32-bit targets, of the lemmas on 64-bit words of `Proof/GcmSiv/Words.lean`,
`Spec.lean` and `Ctr.lean`: a block is four little-endian 32-bit words
`le4 w₀ ++ … ++ le4 w₃`, and a 64-bit word two (`le8_append`). On them:

* POLYVAL's field element of a block and the bytes of one (`ofBytes_le4`,
  `ofBytes_bytesAt`, `toBytes_append4`);
* GHASH's product with `x` (`hkeyOf_words`) and the top bit of a word
  cleared by two shifts (`shl_shr_one`);
* the tag input, the initial counter block and the lengths block
  (`tagOf_words`, `initialCounter_words`, `le64_words`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.GcmSiv.Words32

open VG
open VG.Proof.Cmac (le4 le8 length_le4 length_le8)

/-- The bytes of a 64-bit word made of two 32-bit words. -/
theorem le8_append (a b : BitVec 32) : le8 (a ++ b) = le4 b ++ le4 a := by
  apply List.ext_getElem (by simp [le8, le4])
  intro i h₁ h₂
  have hi : i < 8 := by simpa [le8] using h₁
  simp only [le8, List.getElem_map, List.getElem_range]
  by_cases h4 : i < 4
  · rw [List.getElem_append_left (by simpa [le4] using h4)]
    simp only [le4, List.getElem_map, List.getElem_range]
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and, BitVec.getLsbD_append,
      show 8 * i + j < 32 by omega, ↓reduceIte]
  · rw [List.getElem_append_right (by simpa [le4] using h4)]
    simp only [le4, List.getElem_map, List.getElem_range, length_le4]
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and, BitVec.getLsbD_append,
      show ¬ (8 * i + j < 32) by omega, ↓reduceIte]
    congr 1
    simp only [List.length_map, List.length_range]
    omega

/-- Four words, regrouped as two 64-bit words. -/
theorem append4 (a b c d : BitVec 32) : (a ++ b) ++ (c ++ d) = a ++ b ++ c ++ d := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append]
  rcases (by omega : i < 32 ∨ 32 ≤ i ∧ i < 64 ∨ 64 ≤ i ∧ i < 96 ∨ 96 ≤ i) with h | h | h | h
  · simp only [h, show i < 64 by omega, ↓reduceIte]
  · simp only [show ¬ i < 32 by omega, show i < 64 by omega, show i - 32 < 32 by omega, ↓reduceIte]
  · simp only [show ¬ i < 32 by omega, show ¬ i < 64 by omega, show i - 64 < 32 by omega,
      show ¬ i - 32 < 32 by omega, show i - 32 - 32 < 32 by omega, ↓reduceIte]
    congr 1
  · simp only [show ¬ i < 32 by omega, show ¬ i < 64 by omega, show ¬ i - 64 < 32 by omega,
      show ¬ i - 32 < 32 by omega, show ¬ i - 32 - 32 < 32 by omega, ↓reduceIte]
    congr 1

/-- POLYVAL's field element of a block stored as four little-endian words. -/
theorem ofBytes_le4 (a b c d : BitVec 32) :
    Spec.GcmSiv.ofBytes (le4 a ++ le4 b ++ le4 c ++ le4 d) = d ++ c ++ b ++ a := by
  rw [List.append_assoc, ← VG.Proof.GcmSiv.Words32.le8_append, ← VG.Proof.GcmSiv.Words32.le8_append, VG.Proof.GcmSiv.ofBytes_le8, VG.Proof.GcmSiv.Words32.append4]

/-- POLYVAL's field element of 16 bytes in memory: four little-endian loads. -/
theorem ofBytes_bytesAt (m : Mem) (p : Addr) :
    Spec.GcmSiv.ofBytes (Spec.Aes.bytesAt m p 16) =
      m.readW (p + BitVec.ofNat 64 12) 32 ++ m.readW (p + BitVec.ofNat 64 8) 32 ++
        m.readW (p + BitVec.ofNat 64 4) 32 ++ m.readW p 32 := by
  rw [Proof.Cmac.bytesAt_split4, ← Proof.Cmac.le4_readW, ← Proof.Cmac.le4_readW, ← Proof.Cmac.le4_readW,
    ← Proof.Cmac.le4_readW, VG.Proof.GcmSiv.Words32.ofBytes_le4]

/-- The bytes of a field element made of four words. -/
theorem toBytes_append4 (a b c d : BitVec 32) :
    Spec.GcmSiv.toBytes (a ++ b ++ c ++ d) = le4 d ++ le4 c ++ le4 b ++ le4 a := by
  rw [← VG.Proof.GcmSiv.Words32.append4, VG.Proof.GcmSiv.toBytes_append, VG.Proof.GcmSiv.Words32.le8_append, VG.Proof.GcmSiv.Words32.le8_append, ← List.append_assoc]

/-- The mask of a word's lowest bit, subtracted from zero: all ones if it is set. -/
theorem neg_and1 (x : BitVec 32) :
    0#32 - (x &&& 1#32) = if x.getLsbD 0 then BitVec.allOnes 32 else 0#32 := by
  have h : x &&& 1#32 = if x.getLsbD 0 then 1#32 else 0#32 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have h1 : ∀ i < 32, (1#32).getLsbD i = decide (i = 0) := by decide +kernel
    rw [BitVec.getLsbD_and, h1 i hi]
    by_cases h0 : i = 0
    · subst h0; cases x.getLsbD 0 <;> simp
    · cases x.getLsbD 0 <;> simp [h0, h1 i hi]
  rw [h]; cases x.getLsbD 0 <;> decide

/-- A bit of a word or zero, chosen by `b`. -/
theorem getLsbD_ite {w : Nat} (b : Bool) (x : BitVec w) (i : Nat) :
    (if b then x else 0#w).getLsbD i = (b && x.getLsbD i) := by
  cases b <;> simp

/-- GHASH's product with `x` (`Words.hkeyOf`) as 32-bit operations compute it. -/
theorem hkeyOf_words (w₀ w₁ w₂ w₃ : BitVec 32) :
    ((w₃ >>> 1) ^^^ ((0#32 - (w₀ &&& 1#32)) &&& 0xE1000000#32)) ++ ((w₂ >>> 1) ||| (w₃ <<< 31)) ++
      ((w₁ >>> 1) ||| (w₂ <<< 31)) ++ ((w₀ >>> 1) ||| (w₁ <<< 31)) =
    Words.hkeyOf (w₃ ++ w₂ ++ w₁ ++ w₀) := by
  have hR : ∀ i < 128, Spec.Gcm.R.getLsbD i = (decide (96 ≤ i) && (0xE1000000#32).getLsbD (i - 96)) := by
    decide +kernel
  have h0 : (w₃ ++ w₂ ++ w₁ ++ w₀).getLsbD 0 = w₀.getLsbD 0 := by
    simp only [BitVec.getLsbD_append, Nat.reduceLT, ↓reduceIte]
  have hx : ∀ (b : Bool) (x : Spec.Gcm.Block),
      (if b then (x >>> 1) ^^^ Spec.Gcm.R else x >>> 1) = (x >>> 1) ^^^ (if b then Spec.Gcm.R else 0#128) := by
    intro b x; cases b <;> simp
  have hm : ∀ b : Bool, (if b then BitVec.allOnes 32 else 0#32) &&& 0xE1000000#32 =
      if b then 0xE1000000#32 else 0#32 := by
    intro b; cases b <;> simp
  rw [VG.Proof.GcmSiv.Words32.neg_and1 w₀, Words.hkeyOf, h0, hx, hm]
  generalize w₀.getLsbD 0 = b
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, VG.Proof.GcmSiv.Words32.getLsbD_ite, hR i hi]
  clear hR h0 hx hm
  rcases (by omega : i < 31 ∨ i = 31 ∨ 32 ≤ i ∧ i < 63 ∨ i = 63 ∨ 64 ≤ i ∧ i < 95 ∨ i = 95 ∨
      96 ≤ i ∧ i < 127 ∨ i = 127) with h | rfl | h | rfl | h | rfl | h | rfl <;>
    simp (disch := omega) only [↓reduceIte, decide_true, decide_false, ite_eq_left, ite_eq_right,
      decide_eq_true, decide_eq_false, Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false,
      Bool.not_true, Bool.not_false, Bool.or_false, Bool.false_or, Bool.xor_false, Bool.false_xor, Nat.sub_sub,
      Nat.add_sub_assoc, Nat.reduceAdd, Nat.reduceSub]
  all_goals try simp (disch := decide) only [BitVec.getLsbD_of_ge, Bool.false_or]

/-- The top bit of a word cleared by shifting it out and back. -/
theorem shl_shr_one (x : BitVec 32) : (x <<< 1) >>> 1 = x &&& 0x7FFFFFFF#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hm : ∀ i < 32, (0x7FFFFFFF#32 : BitVec 32).getLsbD i = decide (i < 31) := by decide +kernel
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, hm i hi, BitVec.getLsbD_shiftLeft]
  by_cases h : i < 31
  · simp only [show 1 + i < 32 by omega, decide_true, Bool.true_and, show ¬ (1 + i < 1) by omega,
      decide_false, Bool.not_false, h, Bool.and_true]
    congr 1; omega
  · simp only [show ¬ (1 + i < 32) by omega, decide_false, Bool.false_and, h, Bool.and_false]

/-- A word zero-extended to 64 bits. -/
theorem setWidth_64 (x : BitVec 32) : x.setWidth 64 = 0#32 ++ x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_append]
  by_cases h : i < 32
  · simp [h, show i < 64 by omega]
  · simp [h, BitVec.getLsbD_of_ge x i (by omega)]

/-- The tag input of POLYVAL's result stored as four words and the nonce as three. -/
theorem tagOf_words (a b c d n₀ n₁ n₂ : BitVec 32) :
    VG.Proof.GcmSiv.tagOf (le4 a ++ le4 b ++ le4 c ++ le4 d) (le4 n₀ ++ le4 n₁ ++ le4 n₂) =
      le4 (a ^^^ n₀) ++ le4 (b ^^^ n₁) ++ le4 (c ^^^ n₂) ++ le4 ((d <<< 1) >>> 1) := by
  rw [show le4 a ++ le4 b ++ le4 c ++ le4 d = le8 (b ++ a) ++ le8 (d ++ c) by
      rw [VG.Proof.GcmSiv.Words32.le8_append, VG.Proof.GcmSiv.Words32.le8_append, List.append_assoc],
    show le4 n₀ ++ le4 n₁ = le8 (n₁ ++ n₀) by rw [VG.Proof.GcmSiv.Words32.le8_append], GcmSiv.tagOf_words, VG.Proof.GcmSiv.Words32.setWidth_64,
    BitVec.xor_append, BitVec.xor_append,
    show (0x7FFFFFFFFFFFFFFF#64 : BitVec 64) = 0x7FFFFFFF#32 ++ BitVec.allOnes 32 by decide,
    BitVec.and_append, BitVec.and_allOnes, BitVec.xor_zero, ← VG.Proof.GcmSiv.Words32.shl_shr_one, VG.Proof.GcmSiv.Words32.le8_append, VG.Proof.GcmSiv.Words32.le8_append,
    ← List.append_assoc]

/-- The initial counter block of a tag stored as four words. -/
theorem initialCounter_words (a b c d : BitVec 32) :
    Spec.GcmSiv.initialCounter (le4 a ++ le4 b ++ le4 c ++ le4 d) =
      le4 a ++ le4 b ++ le4 c ++ le4 (d ||| 0x80000000#32) := by
  rw [show le4 a ++ le4 b ++ le4 c ++ le4 d = le8 (b ++ a) ++ le8 (d ++ c) by
      rw [VG.Proof.GcmSiv.Words32.le8_append, VG.Proof.GcmSiv.Words32.le8_append, List.append_assoc],
    GcmSiv.initialCounter_words,
    show (0x8000000000000000#64 : BitVec 64) = 0x80000000#32 ++ 0#32 by decide,
    BitVec.or_append, BitVec.or_zero, VG.Proof.GcmSiv.Words32.le8_append, VG.Proof.GcmSiv.Words32.le8_append, ← List.append_assoc]

/-- `little_endian_uint64(8 x)` of a 32-bit `x`, as two words. -/
theorem le64_words (x : BitVec 32) :
    Spec.GcmSiv.le64 (8 * x.toNat) = le4 (x <<< 3) ++ le4 (x >>> 29) := by
  rw [VG.Proof.GcmSiv.le64_le8, ← VG.Proof.GcmSiv.Words32.le8_append]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  rw [BitVec.toNat_ofNat, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt _),
    Nat.shiftLeft_eq, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  omega

end VG.Proof.GcmSiv.Words32

end
