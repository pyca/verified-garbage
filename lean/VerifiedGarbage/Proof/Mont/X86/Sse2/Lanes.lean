module

public import VerifiedGarbage.TCB.X86.Isa
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword

/-! # SSE2 quadword lanes for the `pmuludq` kernel

The kernel (`Impl/Mont/X86/Sse2.lean`) keeps two 64-bit sums in the two
quadwords of an XMM register; these are its instructions on those lanes
(`qword`): `paddq` and `psrlq` lane by lane, `psrldq` by 8 bytes moving
lane 1 down, `pmuludq` multiplying doublewords 0 and 2, and the doublewords
of what `movq`, `movd` and `pshufd` put in a register.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86

theorem getLsbD_qword (x : BitVec 128) (k i : Nat) :
    (qword x k).getLsbD i = (decide (i < 64) && x.getLsbD (64 * k + i)) := by
  simp only [qword, BitVec.getLsbD_extractLsb']

theorem qword_append_0 (x y : BitVec 64) : qword (x ++ y) 0 = y := by
  simp only [qword, Nat.mul_zero, BitVec.extractLsb'_append_eq_right]

theorem qword_append_1 (x y : BitVec 64) : qword (x ++ y) 1 = x := by
  simp only [qword, Nat.mul_one, BitVec.extractLsb'_append_eq_left]

theorem qword_paddq (a b : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (XBinOp.eval .paddq a b) i = qword a i + qword b i := by
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · exact qword_append_0 _ _
  · exact qword_append_1 _ _

theorem psrlq_eq (a : BitVec 128) :
    XShiftOp.eval .psrlq a 32 = (qword a 1 >>> 32) ++ (qword a 0 >>> 32) := by
  change (if 63 < (32 : BitVec 8).toNat then 0 else
    (qword a 1 >>> (32 : BitVec 8).toNat) ++ (qword a 0 >>> (32 : BitVec 8).toNat)) = _
  rw [ite_eq_right (by decide)]; rfl

theorem qword_psrlq (a : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (XShiftOp.eval .psrlq a 32) i = qword a i >>> 32 := by
  rw [psrlq_eq]
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · exact qword_append_0 _ _
  · exact qword_append_1 _ _

theorem psrldq_eq (a : BitVec 128) : XShiftOp.eval .psrldq a 8 = a >>> 64 := rfl

theorem qword_psrldq_0 (a : BitVec 128) : qword (XShiftOp.eval .psrldq a 8) 0 = qword a 1 := by
  rw [psrldq_eq]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_qword, hi, decide_true, Bool.true_and, BitVec.getLsbD_ushiftRight]
  exact congrArg _ (by omega)

theorem qword_psrldq_1 (a : BitVec 128) : qword (XShiftOp.eval .psrldq a 8) 1 = 0 := by
  rw [psrldq_eq]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_qword, hi, decide_true, Bool.true_and, BitVec.getLsbD_ushiftRight]
  rw [BitVec.getLsbD_of_ge a _ (by omega)]; simp

theorem qword_pmuludq_0 (a b : BitVec 128) :
    qword (pmuludq a b) 0 = (dword a 0).setWidth 64 * (dword b 0).setWidth 64 :=
  qword_append_0 _ _

theorem qword_pmuludq_1 (a b : BitVec 128) :
    qword (pmuludq a b) 1 = (dword a 2).setWidth 64 * (dword b 2).setWidth 64 :=
  qword_append_1 _ _

theorem pxor_self (a : BitVec 128) : XBinOp.eval .pxor a a = 0 := by
  simp only [XBinOp.eval, BitVec.xor_self]; rfl

theorem qword_zero (i : Nat) : qword 0 i = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [getLsbD_qword]

/-- The doublewords of `movq`'s value: the 8 bytes' two words. -/
theorem dword_movq_0 (v : BitVec 64) : dword ((0 : BitVec 64) ++ v) 0 = v.extractLsb' 0 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_dword, hi, decide_true, Bool.true_and, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  simp [show i < 64 by omega]

theorem dword_movq_1 (v : BitVec 64) : dword ((0 : BitVec 64) ++ v) 1 = v.extractLsb' 32 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_dword, hi, decide_true, Bool.true_and, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  rw [ite_eq_left (by omega)]

/-- The doublewords of `movd`'s value. -/
theorem dword_movd_0 (r : BitVec 32) : dword ((0 : BitVec 96) ++ r) 0 = r := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_dword, hi, decide_true, Bool.true_and, BitVec.getLsbD_append]
  simp [hi]

theorem dword_movd_2 (r : BitVec 32) : dword ((0 : BitVec 96) ++ r) 2 = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_dword, hi, decide_true, Bool.true_and, BitVec.getLsbD_append]
  simp [show ¬ 64 + i < 32 by omega]

/-- `pshufd` with `0x10`: doublewords 0 and 1 into doublewords 0 and 2. -/
theorem dword_shuf10_0 (a : BitVec 128) : dword (shufDwords a 0x10) 0 = dword a 0 := by
  rw [dword_shufDwords _ _ (by decide)]; rfl

theorem dword_shuf10_2 (a : BitVec 128) : dword (shufDwords a 0x10) 2 = dword a 1 := by
  rw [dword_shufDwords _ _ (by decide)]; rfl

/-- `pshufd` with `0x01`: doublewords 1 and 0 into doublewords 0 and 2. -/
theorem dword_shuf01_0 (a : BitVec 128) : dword (shufDwords a 0x01) 0 = dword a 1 := by
  rw [dword_shufDwords _ _ (by decide)]; rfl

theorem dword_shuf01_2 (a : BitVec 128) : dword (shufDwords a 0x01) 2 = dword a 0 := by
  rw [dword_shufDwords _ _ (by decide)]; rfl

/-- The two words of an 8-byte read. -/
theorem readW64_lo (m : Mem) (a : Addr) : (m.readW a 64).extractLsb' 0 32 = m.readW a 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, Mem.readW, BitVec.getLsbD_setWidth,
    Nat.zero_add]
  rw [getLsbD_read _ _ (by omega), getLsbD_read _ _ (by omega)]
  simp [show i < 64 by omega]

theorem readW64_hi (m : Mem) (a : Addr) : (m.readW a 64).extractLsb' 32 32 = m.readW (a + 4) 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, Mem.readW, BitVec.getLsbD_setWidth]
  rw [getLsbD_read _ _ (by omega), getLsbD_read _ _ (by omega)]
  simp only [show 32 + i < 64 by omega, decide_true, Bool.true_and]
  rw [show a + BitVec.ofNat 64 ((32 + i) / 8) = a + 4 + BitVec.ofNat 64 (i / 8) by
    rw [show (32 + i) / 8 = 4 + i / 8 by omega, BitVec.ofNat_add, BitVec.add_assoc]; rfl]
  exact congrArg _ (by omega)

/-- A product of two words as a quadword. -/
theorem mul_setWidth (x y : BitVec 32) :
    x.setWidth 64 * y.setWidth 64 = BitVec.ofNat 64 (x.toNat * y.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have hy := y.isLt
  simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 64), Nat.mod_eq_of_lt (by omega : y.toNat < 2 ^ 64)]

end VG.Proof.Mont.X86.Sse2
