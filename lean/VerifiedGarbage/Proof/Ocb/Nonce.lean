import VerifiedGarbage.Proof.Ocb.Spec

/-!
# OCB: the block `Nonce`

Untrusted: everything here is checked by Lean. `Nonce` (§4.2), for a tag of
`t` bytes and a nonce of 1 to 15 bytes, is the block `nonceN t nonce`, whose
byte `k` is `nb t nonce k` (`nonceN_byte`): the nonce at the end, a 1 before
it, and `TAGLEN mod 128` in the top 7 bits, as an implementation writes it
into zeros. `ENCIPHER` takes it with its last 6 bits cleared
(`nonceN_masked_byte`), which are `bottom` (`nonceN_bottom`, `offset0_eq`).
-/

namespace VG.Proof.Ocb

open VG.Spec.Ocb

/-- A number below `2 ^ i` has no bit `j ≥ i`. -/
theorem testBit_ge {x i j : Nat} (hx : x < 2 ^ i) (h : i ≤ j) : x.testBit j = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) h))

/-- Bit `j` of byte `e` (from the right) of big-endian bytes. -/
theorem testBit_beVal (bs : List Byte) (e : Nat) {j : Nat} (hj : j < 8) :
    (Proof.Aes.beVal bs).testBit (8 * e + j) =
      if e < bs.length then (bs.getD (bs.length - 1 - e) 0).getLsbD j else false := by
  split
  · have hd := Proof.Aes.beVal_digit bs (k := bs.length - 1 - e) (by omega)
    rw [show bs.length - 1 - (bs.length - 1 - e) = e by omega] at hd
    rw [BitVec.getLsbD, ← hd, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, Nat.testBit_mod_two_pow,
      Nat.testBit_div_two_pow]
    simp [hj, Nat.add_comm]
  · have := Proof.Aes.beVal_lt bs
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
    exact testBit_ge this (by omega)

/-- The block `Nonce` of §4.2, before its last 6 bits are cleared. -/
def nonceN (t : Nat) (nonce : List Byte) : Block :=
  (BitVec.ofNat 128 (8 * t % 128) <<< 121) ||| ((1 : Block) <<< (8 * nonce.length)) |||
    BitVec.ofNat 128 (nonce.foldl (fun acc b => 256 * acc + b.toNat) 0)

/-- Byte `k` of `zeros ‖ 1 ‖ N`: the nonce at the end and a 1 before it. -/
def nbase (nonce : List Byte) (k : Nat) : Byte :=
  if k = 15 - nonce.length then 1
  else if 16 - nonce.length ≤ k then nonce.getD (k - (16 - nonce.length)) 0 else 0

/-- Byte `k` of `Nonce`, as an implementation writes it: the nonce at the end,
a 1 before it, and `TAGLEN mod 128` in the top 7 bits. -/
def nb (t : Nat) (nonce : List Byte) (k : Nat) : Byte :=
  if k = 0 then nbase nonce k ||| BitVec.ofNat 8 (16 * (t % 16)) else nbase nonce k

/-- The bits of 1. -/
theorem getLsbD_one' {w : Nat} (hw : 0 < w) (i : Nat) : (1 : BitVec w).getLsbD i = decide (i = 0) := by
  rw [show (1 : BitVec w) = 1#w from rfl, BitVec.getLsbD_one]; simp [hw]

/-- The bytes of `Nonce`. -/
theorem nonceN_byte (t : Nat) (nonce : List Byte) (h1 : 1 ≤ nonce.length) (h15 : nonce.length ≤ 15)
    {k : Nat} (hk : k < 16) : (toBytes (nonceN t nonce)).getD k 0 = nb t nonce k := by
  rw [toBytes_eq, Proof.Aes.toBytes_getD _ hk]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hb : nonce.foldl (fun acc b => 256 * acc + b.toNat) 0 = Proof.Aes.beVal nonce := rfl
  simp only [nonceN, hb, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ofNat, getLsbD_one' (show 0 < 128 by decide), hj, decide_true, Bool.true_and,
    show 8 * (15 - k) + j < 128 by omega]
  rw [testBit_beVal nonce (15 - k) hj]
  have e8 : 8 * t % 128 = (t % 16) * 2 ^ 3 := by omega
  rw [e8, Nat.testBit_mul_two_pow]
  unfold nb nbase
  by_cases hk0 : k = 0
  · subst hk0
    have e16 : 16 * (t % 16) = 2 ^ 4 * (t % 16) := rfl
    simp only [↓reduceIte, BitVec.getLsbD_or, e16, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_mul, hj,
      decide_true, Bool.true_and, show ¬ 15 < nonce.length by omega, show ¬ 16 - nonce.length ≤ 0 by omega]
    by_cases hn : nonce.length = 15
    · simp only [hn, ↓reduceIte, getLsbD_one' (show 0 < 8 by decide)]
      rcases (show j = 0 ∨ (1 ≤ j ∧ j < 4) ∨ 4 ≤ j by omega) with rfl | ⟨ha, hb⟩ | ha
      · simp
      · simp [show ¬ 120 + j < 121 by omega, show ¬ 3 ≤ 120 + j - 121 by omega, show ¬ 4 ≤ j by omega,
          show j ≠ 0 by omega]
      · simp [show ¬ 120 + j < 121 by omega, show 3 ≤ 120 + j - 121 by omega, ha, show j ≠ 0 by omega,
          show 120 + j - 121 - 3 = j - 4 by omega, show 120 + j - 121 < 128 by omega]
    · simp only [show (0 = 15 - nonce.length) = False by simp; omega, ↓reduceIte]
      rcases (show j = 0 ∨ (1 ≤ j ∧ j < 4) ∨ 4 ≤ j by omega) with rfl | ⟨ha, hb⟩ | ha
      · simp [show ¬ 120 < 8 * nonce.length by omega, show 120 - 8 * nonce.length ≠ 0 by omega]
      · simp [show ¬ 120 + j < 121 by omega, show ¬ 3 ≤ 120 + j - 121 by omega, show ¬ 4 ≤ j by omega,
          show ¬ 120 + j < 8 * nonce.length by omega, show 120 + j - 8 * nonce.length ≠ 0 by omega]
      · simp [show ¬ 120 + j < 121 by omega, show 3 ≤ 120 + j - 121 by omega, ha,
          show 120 + j - 121 - 3 = j - 4 by omega, show 120 + j - 121 < 128 by omega,
          show ¬ 120 + j < 8 * nonce.length by omega, show 120 + j - 8 * nonce.length ≠ 0 by omega]
  · simp only [hk0, ↓reduceIte, show 8 * (15 - k) + j < 121 by omega, decide_true, Bool.not_true,
      Bool.false_and, Bool.false_or]
    by_cases hkn : k = 15 - nonce.length
    · simp only [hkn, ↓reduceIte, getLsbD_one' (show 0 < 8 by decide),
        show ¬ 15 - (15 - nonce.length) < nonce.length by omega, Bool.or_false]
      rcases (show j = 0 ∨ 0 < j by omega) with rfl | ha
      · simp [show 15 - (15 - nonce.length) = nonce.length by omega]
      · simp [show ¬ 8 * (15 - (15 - nonce.length)) + j < 8 * nonce.length by omega,
          show 8 * (15 - (15 - nonce.length)) + j - 8 * nonce.length ≠ 0 by omega, show j ≠ 0 by omega]
    · simp only [hkn, ↓reduceIte]
      by_cases hkr : 16 - nonce.length ≤ k
      · simp [hkr, show 15 - k < nonce.length by omega, show 8 * (15 - k) + j < 8 * nonce.length by omega,
          show nonce.length - 1 - (15 - k) = k - (16 - nonce.length) by omega]
      · simp [hkr, show ¬ 15 - k < nonce.length by omega, show ¬ 8 * (15 - k) + j < 8 * nonce.length by omega,
          show 8 * (15 - k) + j - 8 * nonce.length ≠ 0 by omega]

/-- The bytes of `~~~63`. -/
theorem mask63_byte : ∀ k < 16, (~~~(63 : Block)).extractLsb' (8 * (15 - k)) 8 =
    if k = 15 then 0xc0 else 0xff := by decide

/-- The bytes of `Nonce` with its last 6 bits cleared. -/
theorem nonceN_masked_byte (t : Nat) (nonce : List Byte) (h1 : 1 ≤ nonce.length) (h15 : nonce.length ≤ 15)
    {k : Nat} (hk : k < 16) :
    (toBytes (nonceN t nonce &&& ~~~(63 : Block))).getD k 0 =
      if k = 15 then nb t nonce 15 &&& 0xc0 else nb t nonce k := by
  rw [toBytes_eq, Proof.Aes.toBytes_getD _ hk, BitVec.extractLsb'_and, mask63_byte k hk,
    ← Proof.Aes.toBytes_getD _ hk, ← toBytes_eq, nonceN_byte t nonce h1 h15 hk]
  split
  · subst_vars; rfl
  · exact BitVec.and_allOnes

/-- `bottom`: the last 6 bits of `Nonce`. -/
theorem nonceN_bottom (t : Nat) (nonce : List Byte) (h1 : 1 ≤ nonce.length) (h15 : nonce.length ≤ 15) :
    ((nonceN t nonce).extractLsb' 0 6).toNat = (nb t nonce 15).toNat % 64 := by
  rw [← nonceN_byte t nonce h1 h15 (by decide), toBytes_eq, Proof.Aes.toBytes_getD _ (by decide),
    BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat]
  simp only [Nat.shiftRight_zero, show 8 * (15 - 15) = 0 from rfl]
  rw [Nat.mod_mod_of_dvd _ (by decide)]

/-- `Offset_0`, from the block of `Nonce` with its last 6 bits cleared and
`bottom`. -/
theorem offset0_eq (ciph : Cipher) (t : Nat) (nonce : List Byte) :
    offset0 ciph t nonce =
      let ktop := ciph (nonceN t nonce &&& ~~~(63 : Block))
      let stretch : BitVec 192 := ktop ++ (ktop.extractLsb' 64 64 ^^^ ktop.extractLsb' 56 64)
      stretch.extractLsb' (64 - ((nonceN t nonce).extractLsb' 0 6).toNat) 128 := rfl

/-- The bytes `zeros ‖ 1 ‖ N`. -/
theorem nbase_list (nonce : List Byte) (h1 : 1 ≤ nonce.length) (h15 : nonce.length ≤ 15) {k : Nat} (hk : k < 16) :
    (zeros (15 - nonce.length) ++ [1] ++ nonce).getD k 0 = nbase nonce k := by
  unfold nbase zeros
  rw [List.getD_eq_getElem?_getD]
  by_cases h₁ : k < 15 - nonce.length
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega)]
    simp [h₁, show k ≠ 15 - nonce.length by omega, show ¬ 16 - nonce.length ≤ k by omega]
  · by_cases h₂ : k = 15 - nonce.length
    · subst h₂
      rw [List.getElem?_append_left (by simp), List.getElem?_append_right (by simp)]
      simp
    · rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_append, List.length_replicate, List.length_singleton, h₂, ↓reduceIte,
        show 16 - nonce.length ≤ k by omega, List.getD_eq_getElem?_getD]
      congr 2; omega

end VG.Proof.Ocb
