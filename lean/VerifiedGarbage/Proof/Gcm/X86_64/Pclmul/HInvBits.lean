import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
import Mathlib.Tactic.SplitIfs

/-!
# GHASH with PCLMULQDQ: the bits of `H · x⁻¹`

What `Impl.Gcm.X86_64.Pclmul.hInv` computes, bit by bit, without the field
(`Proof/Gcm/Poly.lean`), so that the modules that compute it on other
registers need not import its algebra: a shift left by one bit (`shl1`) and
`x⁻¹` if the bit shifted out was set (`mask_eq`).
-/

namespace VG.Proof.Gcm.X86_64.Pclmul

open VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (xInv)

theorem shl1 (h : BitVec 128) :
    XShiftOp.eval .psllq h 1 ||| XShiftOp.eval .pslldq (XShiftOp.eval .psrlq h 63) 8 = h <<< 1 := by
  have e1 : XShiftOp.eval .psllq h 1 = (qword h 1 <<< 1) ++ (qword h 0 <<< 1) := rfl
  have e2 : XShiftOp.eval .psrlq h 63 = (qword h 1 >>> 63) ++ (qword h 0 >>> 63) := rfl
  have e3 : ∀ y, XShiftOp.eval .pslldq y 8 = y <<< 64 := fun _ => rfl
  rw [e1, e2, e3]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, qword, BitVec.getLsbD_extractLsb']
  rcases (by omega : i = 0 ∨ (1 ≤ i ∧ i < 64) ∨ i = 64 ∨ 64 < i) with h | h | h | h
  · subst h; simp
  · simp (disch := omega) only [ite_eq_left, decide_eq_true, decide_eq_false, Bool.true_and,
      Bool.not_false, Bool.false_and, Bool.or_false, Bool.and_false, Bool.and_true, Bool.not_true]
    exact congrArg _ (by omega)
  · subst h; simp
  · simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true, decide_eq_false,
      Bool.true_and, Bool.not_false, Bool.false_and, Bool.or_false, Bool.and_false, Bool.and_true,
      Bool.not_true]
    exact congrArg _ (by omega)

theorem shr31 (y : BitVec 32) : y >>> 31 = if y.msb then 1#32 else 0#32 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.msb_eq_decide, Nat.shiftRight_eq_div_pow]
  have := y.isLt
  by_cases h : 2 ^ (32 - 1) ≤ y.toNat
  · simp only [h, decide_true, ite_true, BitVec.toNat_ofNat]; omega
  · simp only [h, decide_false, Bool.false_eq_true, ite_false, BitVec.toNat_ofNat]; omega

theorem msb_dword3 (h : BitVec 128) : dword h 3 >>> 31 = if h.getMsbD 0 then 1#32 else 0#32 := by
  have e : (dword h 3).msb = h.getMsbD 0 := by
    simp only [BitVec.msb_eq_getLsbD_last, getLsbD_dword, BitVec.getMsbD]; rfl
  rw [shr31, e]

/-- The mask of `hInv`: `x⁻¹` if the bit shifted out of `h` is 1, else 0. -/
theorem mask_eq (h : BitVec 128) :
    XBinOp.eval .pandn (XBinOp.eval .paddd (XShiftOp.eval .psrld (shufDwords h 0xff) 31)
      (XBinOp.eval .punpcklqdq ((0 : BitVec 64) ++ (0xffffffffffffffff : BitVec 64))
        ((0 : BitVec 64) ++ (0xffffffffffffffff : BitVec 64)))) xInv =
      if h.getMsbD 0 then xInv else 0 := by
  have e0 : shufDwords h 0xff = ofDwords (dword h 3) (dword h 3) (dword h 3) (dword h 3) := rfl
  have e1 : ∀ a, XShiftOp.eval .psrld a 31 =
      ofDwords (dword a 0 >>> 31) (dword a 1 >>> 31) (dword a 2 >>> 31) (dword a 3 >>> 31) :=
    fun _ => rfl
  have e2 : XBinOp.eval .punpcklqdq ((0 : BitVec 64) ++ (0xffffffffffffffff : BitVec 64))
      ((0 : BitVec 64) ++ (0xffffffffffffffff : BitVec 64)) = ofDwords (-1) (-1) (-1) (-1) := by rfl
  rw [e0, e1, e2]
  simp only [dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3, msb_dword3]
  split_ifs
  · simp only [XBinOp.eval, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3,
      show (1#32 : BitVec 32) + -1 = 0 by rfl, show ofDwords 0 0 0 0 = 0 by rfl]
    rfl
  · simp only [XBinOp.eval, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3,
      show (0#32 : BitVec 32) + -1 = -1 by rfl,
      show ~~~ofDwords (-1) (-1) (-1) (-1) = 0 by rfl]
    rfl

end VG.Proof.Gcm.X86_64.Pclmul
