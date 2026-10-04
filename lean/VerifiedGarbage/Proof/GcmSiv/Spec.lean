import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Mem32
import VerifiedGarbage.Spec.GcmSiv

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
  aesWith_length _ _ _

/-- The four bytes of the counter `i`, as `little_endian_uint32`. -/
theorem le4_le32 (i : Nat) : Proof.Cmac.le4 ((BitVec.ofNat 64 i).setWidth 32) = Spec.GcmSiv.le32 i := by
  apply List.ext_getElem (by simp [Proof.Cmac.le4, Spec.GcmSiv.le32])
  intro j h₁ _
  have hj : j < 4 := by simpa [Proof.Cmac.le4] using h₁
  simp only [Proof.Cmac.le4, Spec.GcmSiv.le32, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> simp <;> omega

/-- The first 8 bytes of `CIPH(little_endian_uint32(i) ‖ nonce)`, for `i < k`,
one after the other. -/
def halves (ciph : Spec.GcmSiv.Cipher) (nonce : List Byte) (k : Nat) : List Byte :=
  (List.range k).flatMap fun i => (ciph (Spec.GcmSiv.le32 i ++ nonce)).take 8

theorem halves_succ (ciph : Spec.GcmSiv.Cipher) (nonce : List Byte) (k : Nat) :
    halves ciph nonce (k + 1) = halves ciph nonce k ++ (ciph (Spec.GcmSiv.le32 k ++ nonce)).take 8 := by
  simp [halves, List.range_succ, List.flatMap_append]

theorem length_halves {ciph : Spec.GcmSiv.Cipher} (h : ∀ x, (ciph x).length = 16) (nonce : List Byte) (k : Nat) :
    (halves ciph nonce k).length = 8 * k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [halves_succ, List.length_append, ih, List.length_take, h]; omega

/-- `derive_keys`: the first 16 bytes of the halves, and the rest. -/
theorem deriveKeys_eq {ciph : Spec.GcmSiv.Cipher} (h : ∀ x, (ciph x).length = 16) (keyLen : Nat)
    (nonce : List Byte) :
    Spec.GcmSiv.deriveKeys ciph keyLen nonce =
      ((halves ciph nonce (keyLen / 8 + 2)).take 16, (halves ciph nonce (keyLen / 8 + 2)).drop 16) := by
  have e : halves ciph nonce (keyLen / 8 + 2) =
      ((ciph (Spec.GcmSiv.le32 0 ++ nonce)).take 8 ++ (ciph (Spec.GcmSiv.le32 1 ++ nonce)).take 8) ++
        (List.range (keyLen / 8)).flatMap fun i => (ciph (Spec.GcmSiv.le32 (i + 2) ++ nonce)).take 8 := by
    simp only [halves, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.append_assoc]
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
  omega

/-- POLYVAL's field element of a block stored as two little-endian words. -/
theorem ofBytes_le8 (a b : BitVec 64) : Spec.GcmSiv.ofBytes (Proof.Cmac.le8 a ++ Proof.Cmac.le8 b) = b ++ a := by
  apply BitVec.eq_of_toNat_eq
  rw [Spec.GcmSiv.ofBytes, BitVec.toNat_ofNat, leNat_append, leNat_le8, leNat_le8, Proof.Cmac.length_le8,
    BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt a.isLt, Nat.shiftLeft_eq]
  have := a.isLt; have := b.isLt
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- POLYVAL's field element of 16 bytes in memory: two little-endian loads. -/
theorem ofBytes_bytesAt (m : Mem) (p : Addr) :
    Spec.GcmSiv.ofBytes (Spec.Aes.bytesAt m p 16) = m.readW (p + BitVec.ofNat 64 8) 64 ++ m.readW p 64 := by
  rw [Proof.Cmac.bytesAt_split, ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW, ofBytes_le8]

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
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega

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
    rw [elems_cons (bs := xs ++ ys) (by simp; omega), elems_cons (bs := xs) (by omega),
      List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega),
      ih _ (by simp; omega), List.cons_append]

theorem elems_append {xs ys : List Byte} (hx : xs.length % 16 = 0) : elems (xs ++ ys) = elems xs ++ elems ys :=
  elems_append_aux ys (xs.length / 16) xs (by omega)

theorem elems_single {bs : List Byte} (h : bs.length = 16) : elems bs = [ofBytes bs] := by
  rw [elems_cons (by omega), List.take_of_length_le (by omega), elems_of_lt (by simp; omega)]

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
  simp [pad16, zeros]

theorem pad16_mod (bs : List Byte) : (pad16 bs).length % 16 = 0 := by
  rw [length_pad16]; omega

/-- A string padded: its whole blocks, then its last bytes padded. -/
theorem pad16_split (bs : List Byte) :
    pad16 bs = bs.take (16 * (bs.length / 16)) ++ pad16 (bs.drop (16 * (bs.length / 16))) := by
  simp only [pad16, List.length_drop, ← List.append_assoc, List.take_append_drop]
  congr 3; omega

/-- The field elements of a padded string. -/
theorem elems_pad16 (bs : List Byte) :
    elems (pad16 bs) = elems (bs.take (16 * (bs.length / 16))) ++
      (if bs.length % 16 = 0 then [] else [ofBytes (bs.drop (16 * (bs.length / 16)) ++ zeros (16 - bs.length % 16))]) := by
  rw [pad16_split, elems_append (by simp; omega)]
  congr 1
  split
  · rename_i h
    rw [List.drop_eq_nil_of_le (by omega)]; rfl
  · rename_i h
    rw [pad16, List.length_drop, elems_single (by simp [zeros]; omega)]
    congr 3
    have : bs.length - 16 * (bs.length / 16) = bs.length % 16 := by omega
    rw [this, Nat.mod_mod, Nat.mod_eq_of_lt (a := 16 - bs.length % 16) (by omega)]

end VG.Proof.GcmSiv
