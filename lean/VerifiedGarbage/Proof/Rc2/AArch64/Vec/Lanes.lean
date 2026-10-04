import VerifiedGarbage.Impl.Rc2.AArch64.CbcVec
import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.Framework.AArch64.Simd

/-!
# RC2 words in 32-bit lanes

The vector decryption keeps word `i` of block `b` of set `h` in the low 16
bits of lane `b` of `wreg h i` (`lw`, `VWords`); the high 16 bits are not
kept. These are the lane facts about the operations it uses: the bitwise
ones and subtraction act on each lane's low 16 bits alone, and masking,
shifting right by `s` and inserting the word shifted left by `16 - s`
rotates it right by `s` (`ror_lane`).
-/

namespace VG.Proof.Rc2.AArch64.Vec

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Tbl.AArch64 VG.Impl.Rc2.AArch64.Vec

/-- The low 16 bits of lane `b`. -/
abbrev lw (x : BitVec 128) (b : Nat) : BitVec 16 := (vword x b).setWidth 16

/-- The words of set `h`: word `i` of block `b` is `vs b`'s. -/
def VWords (s : State) (h : Nat) (vs : Nat → Spec.Rc2.State) : Prop :=
  ∀ i < 4, ∀ b < 4, lw (s.v (wreg h i)) b = (vs b).getD i 0

theorem vword_and (x y : BitVec 128) (c : Nat) : vword (x &&& y) c = vword x c &&& vword y c := by
  ext i hi
  simp [vword, BitVec.getElem_extractLsb', BitVec.getElem_and]

theorem vword_bic (x y : BitVec 128) (c : Nat) :
    vword (x &&& ~~~y) c = vword x c &&& ~~~vword y c := by
  ext i hi
  simp only [vword, BitVec.getElem_extractLsb', BitVec.getElem_and, BitVec.getElem_not,
    BitVec.getLsbD_and, BitVec.getLsbD_not]
  by_cases h : 32 * c + i < 128
  · simp [h]
  · simp [h, BitVec.getLsbD_of_ge x (32 * c + i) (by omega)]

theorem vword_not (x : BitVec 128) {c : Nat} (hc : c < 4) : vword (~~~x) c = ~~~vword x c := by
  ext i hi
  simp [vword, BitVec.getElem_extractLsb', BitVec.getElem_not, show 32 * c + i < 128 by omega]

theorem vword_xor (x y : BitVec 128) (c : Nat) : vword (x ^^^ y) c = vword x c ^^^ vword y c := by
  simp only [vword, BitVec.extractLsb'_xor]

theorem vword_or (x y : BitVec 128) (c : Nat) : vword (x ||| y) c = vword x c ||| vword y c := by
  ext i hi
  simp [vword, BitVec.getElem_extractLsb', BitVec.getElem_or]

theorem setWidth16_sub (x y : BitVec 32) : (x - y).setWidth 16 = x.setWidth 16 - y.setWidth 16 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub]
  omega

theorem setWidth16_and (x y : BitVec 32) : (x &&& y).setWidth 16 = x.setWidth 16 &&& y.setWidth 16 := by
  ext i hi; simp

theorem setWidth16_not (x : BitVec 32) : (~~~x).setWidth 16 = ~~~(x.setWidth 16) := by
  ext i hi; simp [show i < 32 by omega]

theorem bit65535 (k : Nat) : (65535 : BitVec 32).getLsbD k = decide (k < 16) := by
  rw [show (65535 : BitVec 32) = BitVec.ofNat 32 (2 ^ 16 - 1) from rfl, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one]
  by_cases h : k < 16
  · simp [h, show k < 32 by omega]
  · simp [h]

/-- Masking, shifting right by `s` and inserting the masked word shifted left
by `16 - s`: the low 16 bits rotated right by `s`. -/
theorem ror_lane (x : BitVec 32) {s : Nat} (h1 : 1 ≤ s) (h2 : s < 16) :
    ((((x &&& 65535) >>> s) &&& ~~~(BitVec.allOnes 32 <<< (16 - s))) |||
      ((x &&& 65535) <<< (16 - s))).setWidth 16 = (x.setWidth 16).rotateRight s := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes,
    BitVec.getLsbD_rotateRight, hj, decide_true, Bool.true_and, Nat.mod_eq_of_lt h2, bit65535]
  by_cases hs : j < 16 - s
  · simp (disch := omega) [hs, show j < 32 by omega, show s + j < 16 by omega]
  · simp (disch := omega) [hs, show j < 32 by omega, show ¬ s + j < 16 by omega,
      show j - (16 - s) < 16 by omega]

end VG.Proof.Rc2.AArch64.Vec
