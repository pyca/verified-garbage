module

public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Rounds
public import VerifiedGarbage.Proof.AesCbc.Spec
public import VerifiedGarbage.Proof.AesXts.Alpha16
import VerifiedGarbage.Proof.AesXts.Alpha
import VerifiedGarbage.Proof.AesXts.Spec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem

/-!
# One-pass XTS-AES on AArch64: blocks and tweaks as words

The one-pass functions (`Impl/AesXts/AArch64Aes.lean`) hold blocks and
tweaks as 128-bit words, in vector registers and in memory, and the tweak
also as its two 64-bit halves in `x14` and `x15`. A word's bytes are `b16`
of it (`bytesAt_b16`, `st_toList`); XOR of words is XOR of their bytes
(`b16_xor`); and the cipher of a register's state is the cipher of its bytes
(`ciphOf_b16`). `xts_word`: the XTS of a block from its words, as the
functions compute it. `mulA128_append`: `AArch64Aes.mulA` on the halves is
`mulA128` on the word, and `twW t k`, the tweak `k` blocks on as a word, has
the bytes of `Spec.Xts.next` (`b16_twW`).
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64.Aes

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesXts (b16 mulA128)
open VG.Proof.Aes.AArch64.Aese (st ext_vbyte vbyte_readW)
open VG.Proof.AesCbc (ciphOf)

theorem bytesAt_b16 (m : Mem) (p : Addr) : bytesAt m p 16 = b16 (m.readW p 128) :=
  AesXts.bytesAt_readW (k := 16) m p

theorem b16_xor (a b : BitVec 128) : b16 (a ^^^ b) = Spec.Cbc.xor (b16 a) (b16 b) := by
  apply List.ext_getElem (by simp [b16, Spec.Cbc.xor])
  intro k h₁ h₂
  have hk : k < 16 := by simpa [b16] using h₁
  simp only [b16, Spec.Cbc.xor, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  ext j hj
  simp

theorem st_toList (v : BitVec 128) : (st v).toList = b16 v := by
  apply List.ext_getElem (by simp [b16])
  intro i h₁ h₂
  simp [st, b16, vbyte]

/-- The function of states of a direction: the cipher or its inverse. -/
def stF (enc : Bool) (nr : Nat) (w : List Byte) : Spec.Aes.State → Spec.Aes.State :=
  if enc then Spec.Aes.cipher nr w else Spec.Aes.invCipher nr w

theorem ciphOf_b16 (enc : Bool) (nr : Nat) (w : List Byte) (v : BitVec 128) :
    ciphOf enc nr w (b16 v) = (stF enc nr w (st v)).toList := by
  have e : (Vector.ofFn fun i : Fin 16 => (b16 v).getD i.1 0) = st v := by
    apply Vector.ext
    intro i hi
    simp [b16, st, vbyte]
  cases enc
  · simp only [ciphOf, stF, Bool.false_eq_true, ↓reduceIte, Spec.Cbc.aesInvWith, e]
  · simp only [ciphOf, stF, ↓reduceIte, Spec.Cbc.aesWith, e]

/-- A block `d` through XTS with the tweak `t`, as words, when `c` is the
word of the cipher of `d ⊕ t`'s state. -/
theorem xts_word (enc : Bool) (nr : Nat) (w : List Byte) (d t c : BitVec 128)
    (hc : st c = stF enc nr w (st (d ^^^ t))) :
    b16 (c ^^^ t) = Spec.Xts.block (ciphOf enc nr w) (b16 t) (b16 d) := by
  rw [Spec.Xts.block, b16_xor, ← st_toList c, hc, ← ciphOf_b16, b16_xor]

/-! ## The tweak -/

/-- The low half of the tweak times `α`, from its halves. -/
def mulLo (lo hi : BitVec 64) : BitVec 64 := (lo <<< 1) ^^^ (if hi.msb then (0x87 : BitVec 64) else 0)

/-- The high half of the tweak times `α`, from its halves. -/
def mulHi (lo hi : BitVec 64) : BitVec 64 := (hi <<< 1) ||| (if lo.msb then (1 : BitVec 64) else 0)

theorem msb_append64 (lo hi : BitVec 64) : (hi ++ lo).msb = hi.msb := by
  simp only [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_append]; rfl
theorem k87 {i : Nat} (h : i < 64) : (135#128)[i] = (135#64)[i] := by
  rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat, BitVec.getLsbD_ofNat]
  simp [h]; omega
theorem k87' {i : Nat} (h : 64 ≤ i) (h' : i < 128) : (135#128)[i] = false := by
  rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat]
  simp [h']; exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) h))
theorem k1 {j : Nat} (h : j < 64) (h0 : j ≠ 0) : (1#64)[j] = false := by
  rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat]
  simp only [h, decide_true, Bool.true_and]; exact Nat.testBit_lt_two_pow (Nat.one_lt_two_pow h0)
theorem mulA128_append (lo hi : BitVec 64) : mulA128 (hi ++ lo) = mulHi lo hi ++ mulLo lo hi := by
  rw [mulA128, msb_append64, mulHi, mulLo]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or]
  rw [BitVec.msb_eq_getLsbD_last, BitVec.msb_eq_getLsbD_last]
  simp only [Nat.add_one_sub_one]
  by_cases h64 : i < 64
  · by_cases h0 : i = 0
    · subst h0; cases hi.getLsbD 63 <;> simp
    · have : ¬ i < 1 := by omega
      cases hi.getLsbD 63 <;> simp [h64, this, show i - 1 < 64 by omega, hi', k87 h64]
  · by_cases h0 : i = 64
    · subst h0; cases hi.getLsbD 63 <;> cases lo.getLsbD 63 <;> simp [k87']
    · have : ¬ i - 64 < 1 := by omega
      cases hi.getLsbD 63 <;> cases lo.getLsbD 63 <;>
        simp [h64, this, show ¬ i - 1 < 64 by omega, hi', k87' (by omega) hi', k1 (show i - 64 < 64 by omega) (by omega),
          show i - 1 - 64 = i - 64 - 1 by omega, show i - 64 < 64 by omega] <;> omega
/-- `dup v.2d, lo` then `ins v.d[1], hi`. -/
theorem setLane_dup (lo hi : BitVec 64) : setLane (ofVDwords lo lo) 64 1 hi = hi ++ lo := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [setLane, ofVDwords, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, BitVec.getLsbD_append]
  by_cases h : i < 64 <;> simp [h, hi', show i - 64 < 64 by omega, show i - 64 < 128 by omega]

/-- The tweak `k` blocks on from `t`, as a word. -/
def twW (t : BitVec 128) (k : Nat) : BitVec 128 := Nat.repeat mulA128 k t

theorem twW_succ (t : BitVec 128) (k : Nat) : twW t (k + 1) = mulA128 (twW t k) := rfl

theorem b16_twW (t : BitVec 128) : ∀ k, b16 (twW t k) = Spec.Xts.next (b16 t) k
  | 0 => rfl
  | k + 1 => by rw [twW_succ, AesXts.mulAlpha_b16, b16_twW t k, AesXts.next_succ]

theorem vbyte_append_lo (x y : BitVec 64) {i : Nat} (h : i < 8) : vbyte (x ++ y) i = y.extractLsb' (8 * i) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [vbyte, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_append]; simp [show 8 * i + j < 64 by omega]
theorem vbyte_append_hi (x y : BitVec 64) {i : Nat} (h : 8 ≤ i) (h' : i < 16) :
    vbyte (x ++ y) i = x.extractLsb' (8 * (i - 8)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [vbyte, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_append]; simp [show ¬ 8 * i + j < 64 by omega]
  exact congrArg _ (by omega)
/-- 16 bytes as two doublewords. -/
theorem readW128 (m : Mem) (a : Addr) : m.readW a 128 = m.readW (a + BitVec.ofNat 64 8) 64 ++ m.readW a 64 := by
  apply ext_vbyte; intro i hi
  rw [vbyte_readW _ _ hi]
  by_cases h : i < 8
  · rw [vbyte_append_lo _ _ h]; simp only [Mem.readW, BitVec.setWidth_eq]
    exact (Mem.extractLsb'_read m a (n := 8) h).symm
  · rw [vbyte_append_hi _ _ (by omega) hi]; simp only [Mem.readW, BitVec.setWidth_eq]
    rw [Mem.extractLsb'_read m _ (n := 8) (show i - 8 < 8 by omega), Offset.add_add_eq a (show 8 + (i - 8) = i by omega)]

end VG.Proof.AesXts.AArch64.Aes
