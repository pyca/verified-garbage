module

public import VerifiedGarbage.Proof.Cmac.Dbl
public import VerifiedGarbage.Proof.Cmac.Mem
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# CMAC: doubling a block in two byte-reversed 64-bit words

For targets that load a block as two byte-reversed words, the high and low
halves of the block as a big-endian integer (`blockAt_byteRev`), double the
integer a word at a time (`dbl_words`, with `0x87` masked by `0 − (hi >> 63)`,
`mask_eq`), and store the halves byte-reversed again (`le8_byteRev`), as
AArch64's `subkeys` does (`Proof/CmacAes/AArch64/Subkeys.lean`), stated for
`byteRev64`, which the targets' byte reversals unfold to.
-/

@[expose] public section

namespace VG.Proof.Cmac

open VG Spec.Cmac

theorem getD_le8_append (a b : BitVec 64) {k : Nat} (hk : k < 16) :
    (le8 a ++ le8 b).getD k 0 = if k < 8 then a.extractLsb' (8 * k) 8 else b.extractLsb' (8 * (k - 8)) 8 := by
  rw [List.getD_eq_getElem?_getD]
  split
  · rw [List.getElem?_append_left (by rw [length_le8]; omega), ← List.getD_eq_getElem?_getD, getD_le8 _ ‹_›]
  · rw [List.getElem?_append_right (by rw [length_le8]; omega), length_le8, ← List.getD_eq_getElem?_getD,
      getD_le8 _ (by omega)]

/-- Storing the byte-reversed halves of `h ++ l` stores its bytes, big-endian. -/
theorem le8_byteRev (h l : BitVec 64) :
    le8 (byteRev64 h) ++ le8 (byteRev64 l) = Spec.Gcm.toBytes (h ++ l) := by
  refine ext16 (by simp [length_le8]) (toBytes_length _) fun k hk => ?_
  rw [Proof.Aes.toBytes_getD _ hk]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp only [hj, decide_true, Bool.true_and]
  rcases Nat.lt_or_ge k 8 with h8 | h8
  · rw [getD_le8_append _ _ hk]
    simp only [h8, ↓reduceIte]
    rw [BitVec.getLsbD_extractLsb', Proof.Gcm.getLsbD_byteRev64 _ _ (by omega)]
    simp only [hj, decide_true, Bool.true_and, show ¬ 8 * (15 - k) + j < 64 by omega, ite_false]
    congr 1; omega
  · rw [getD_le8_append _ _ hk]
    simp only [show ¬ k < 8 by omega, ↓reduceIte]
    rw [BitVec.getLsbD_extractLsb', Proof.Gcm.getLsbD_byteRev64 _ _ (by omega)]
    simp only [hj, decide_true, Bool.true_and, show 8 * (15 - k) + j < 64 by omega, ite_true]
    congr 1; omega

theorem mask_eq (hi : BitVec 64) :
    ((0 : BitVec 64) - (hi >>> 63)) &&& 0x87 = if hi.msb then 0x87 else 0 := by
  have h : hi >>> 63 = if hi.msb then 1 else 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.msb_eq_decide]
    have := hi.isLt
    by_cases hm : 2 ^ (64 - 1) ≤ hi.toNat
    · rw [decide_eq_true hm]; simp; omega
    · rw [decide_eq_false hm]; simp; omega
  rw [h]
  split <;> decide

theorem bit135 : ∀ p < 64, (135 : BitVec 64).getLsbD p = (135 : BitVec 128).getLsbD p := by decide

/-- The words a doubling stores, from the halves `hi` and `lo` it loads. -/
def dblHi (hi lo : BitVec 64) : BitVec 64 := (hi <<< 1) ||| (lo >>> 63)
def dblLo (hi lo : BitVec 64) : BitVec 64 := (lo <<< 1) ^^^ (((0 : BitVec 64) - (hi >>> 63)) &&& 0x87)

/-- The doubling of `hi ++ lo`. -/
theorem dbl_words (hi lo : BitVec 64) : dblHi hi lo ++ dblLo hi lo = dbl128 (hi ++ lo) := by
  rw [dblHi, dblLo, mask_eq, dbl128, BitVec.msb_append]
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [BitVec.getLsbD_append]
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append, hp, decide_true, Bool.true_and]
  have h0 : ((64 : Nat) = 0) = False := by simp
  simp only [h0, ite_false]
  by_cases h64 : p < 64
  · simp only [h64, ↓reduceIte, show p - 1 < 64 by omega, decide_true, Bool.true_and]
    congr 1
    split
    · exact bit135 p h64
    · simp
  · have hm : (if hi.msb = true then (135 : BitVec 128) else 0).getLsbD p = false := by
      split
      · exact high_0x87 (by omega)
      · simp
    rw [hm, Bool.xor_false]
    simp only [h64, ↓reduceIte, show p - 64 < 64 by omega, decide_true, Bool.true_and]
    rcases Nat.eq_or_lt_of_le (show 64 ≤ p by omega) with rfl | hlt
    · simp
    · rw [BitVec.getLsbD_of_ge lo (63 + (p - 64)) (by omega)]
      simp [show ¬ p - 64 < 1 by omega, show ¬ p < 1 by omega, show ¬ p - 1 < 64 by omega]
      congr 1

/-- Two byte-reversed 8-byte loads read a block. -/
theorem blockAt_byteRev (m : Mem) (p : Addr) :
    byteRev64 (m.readW (p + BitVec.ofNat 64 0) 64) ++ byteRev64 (m.readW (p + BitVec.ofNat 64 8) 64) =
      Spec.Gcm.blockAt m p := by
  have e : ∀ j : Nat, j < 15 → p + BitVec.ofNat 64 j + 1 = p + BitVec.ofNat 64 (j + 1) :=
    fun j _ => Offset.add_add p j 1
  rw [byteRev64_readW, byteRev64_readW]
  simp only [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide),
    e 5 (by decide), e 6 (by decide), e 8 (by decide), e 9 (by decide), e 10 (by decide), e 11 (by decide),
    e 12 (by decide), e 13 (by decide), e 14 (by decide)]
  rw [Spec.Gcm.blockAt, show Spec.Aes.bytesAt m p 16 =
    [m (p + BitVec.ofNat 64 0), m (p + BitVec.ofNat 64 1), m (p + BitVec.ofNat 64 2),
      m (p + BitVec.ofNat 64 3), m (p + BitVec.ofNat 64 4), m (p + BitVec.ofNat 64 5),
      m (p + BitVec.ofNat 64 6), m (p + BitVec.ofNat 64 7), m (p + BitVec.ofNat 64 8),
      m (p + BitVec.ofNat 64 9), m (p + BitVec.ofNat 64 10), m (p + BitVec.ofNat 64 11),
      m (p + BitVec.ofNat 64 12), m (p + BitVec.ofNat 64 13), m (p + BitVec.ofNat 64 14),
      m (p + BitVec.ofNat 64 15)] from rfl, Proof.Gcm.ofBytes_16]

/-- A block doubled by two byte-reversed loads and stores of 64-bit words. -/
theorem dbl_byteRev (m : Mem) (p : Addr) :
    le8 (byteRev64 (dblHi (byteRev64 (m.readW (p + BitVec.ofNat 64 0) 64))
        (byteRev64 (m.readW (p + BitVec.ofNat 64 8) 64)))) ++
      le8 (byteRev64 (dblLo (byteRev64 (m.readW (p + BitVec.ofNat 64 0) 64))
        (byteRev64 (m.readW (p + BitVec.ofNat 64 8) 64)))) =
      dbl 16 (Spec.Aes.bytesAt m p 16) := by
  rw [le8_byteRev, dbl_words, blockAt_byteRev, dbl_eq (bytesAt_length _ _ _), Spec.Gcm.blockAt]

end VG.Proof.Cmac
