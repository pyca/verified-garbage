import VerifiedGarbage.Proof.Blowfish.X86_64.Scan
import VerifiedGarbage.Proof.Framework.X86_64.Sse

/-! # The OR of a plane accumulator's words -/

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.Impl.Blowfish.X86_64

/-- What `reduce` leaves of `a`. -/
def reduceV (a : BitVec 128) : BitVec 128 :=
  let a1 := a ||| shufDwords a 0x4E
  let a2 := a1 ||| shufDwords a1 0xB1
  let a3 := a2 ||| XShiftOp.eval .psrld a2 16
  XShiftOp.eval .psrld (XShiftOp.eval .pslld a3 16) 16

theorem dword_or (a b : BitVec 128) (k : Nat) : dword (a ||| b) k = dword a k ||| dword b k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_dword, BitVec.getLsbD_or, decide_eq_true hi, Bool.true_and]

theorem psrld_dwords (a : BitVec 128) (c : BitVec 8) (hn : c.toNat < 32) :
    XShiftOp.eval .psrld a c =
      ofDwords (dword a 0 >>> c.toNat) (dword a 1 >>> c.toNat) (dword a 2 >>> c.toNat) (dword a 3 >>> c.toNat) := by
  simp only [XShiftOp.eval, show ¬ 31 < c.toNat by omega, ite_false]

theorem pslld_dwords (a : BitVec 128) (c : BitVec 8) (hn : c.toNat < 32) :
    XShiftOp.eval .pslld a c =
      ofDwords (dword a 0 <<< c.toNat) (dword a 1 <<< c.toNat) (dword a 2 <<< c.toNat) (dword a 3 <<< c.toNat) := by
  simp only [XShiftOp.eval, show ¬ 31 < c.toNat by omega, ite_false]

theorem reduceV_dword (a : BitVec 128) :
    dword (reduceV a) 0 =
      let D := (dword a 0 ||| dword a 2) ||| (dword a 1 ||| dword a 3)
      ((D ||| D >>> 16) <<< 16) >>> 16 := by
  simp only [reduceV]
  rw [psrld_dwords _ _ (by decide), pslld_dwords _ _ (by decide), psrld_dwords _ _ (by decide)]
  simp only [dword_ofDwords_0, dword_or]
  rw [show shufDwords a 0x4E = ofDwords (dword a 2) (dword a 3) (dword a 0) (dword a 1) from rfl,
    shufDwords_b1]
  simp only [dword_ofDwords_0, dword_ofDwords_1, dword_or]
  rfl

theorem dword_words (v : BitVec 128) (k : Nat) : dword v k = word v (2 * k + 1) ++ word v (2 * k) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_dword, BitVec.getLsbD_append, getLsbD_word, decide_eq_true hi, Bool.true_and]
  split
  · simp only [decide_eq_true ‹i < 16›, Bool.true_and]; exact congrArg _ (by omega)
  · simp only [decide_eq_true (show i - 16 < 16 by omega), Bool.true_and]; exact congrArg _ (by omega)

theorem reduce_scan (p : Nat → Byte) {x : Nat} (hx : x < 256) :
    dword (reduceV (scanAcc p x 16)) 0 = (p x).setWidth 32 := by
  have hw : ∀ w < 8, word (scanAcc p x 16) w = if x % 16 / 2 = w then (p x).setWidth 16 else 0 := by
    intro w hw; rw [scanAcc, word_ofWords _ hw]
    simp only [show x / 16 < 16 by omega, true_and]
  rw [reduceV_dword, dword_words, dword_words, dword_words, dword_words]
  simp only [Nat.mul_zero, Nat.zero_add, show 2 * 2 = 4 by rfl, show 2 * 3 = 6 by rfl,
    show 2 * 2 + 1 = 5 by rfl, show 2 * 3 + 1 = 7 by rfl, show 2 * 1 + 1 = 3 by rfl, show 2 * 1 = 2 by rfl,
    hw _ (by decide : 0 < 8), hw _ (by decide : 1 < 8), hw _ (by decide : 2 < 8), hw _ (by decide : 3 < 8),
    hw _ (by decide : 4 < 8), hw _ (by decide : 5 < 8), hw _ (by decide : 6 < 8), hw _ (by decide : 7 < 8)]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have h8 : x % 16 / 2 < 8 := by omega
  generalize x % 16 / 2 = w at h8
  rcases (by omega : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5 ∨ w = 6 ∨ w = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp (disch := omega) only [reduceCtorEq, ite_true, ite_false, show ¬ (0 = 1) by decide]
    by_cases h : i < 16
    · have h' : 16 + i < 32 := by omega
      have h'' : ¬ 16 + i < 16 := by omega
      simp only [h, h', h'', BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or,
        BitVec.getLsbD_append, hi, BitVec.getLsbD_setWidth, decide_true, decide_false, Bool.not_false,
        Bool.true_and, ite_true, ite_false,
        show 16 + i - 16 = i by omega]
      by_cases h8 : i < 8 <;> simp [h8]
    · have h' : ¬ 16 + i < 32 := by omega
      simp [h', BitVec.getLsbD_shiftLeft, hi]
      exact BitVec.getLsbD_of_ge (p x) i (by omega)

end VG.Proof.Blowfish.X86_64
