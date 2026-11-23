module
public import VerifiedGarbage.TCB.X86.Sse

import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem

/-!
# x86 (32-bit): SSE values as words

The SSE2 instructions on 16-bit words, stated on the words of their
operands (`word`, `ofWords`), and 128-bit loads and stores as eight 16-bit
words, as `Proof/Framework/X86_64/Words.lean` has them for x86-64.
-/

@[expose] public section

namespace VG.X86

/-- Two values are equal if their words are. -/
theorem ext_word {x y : BitVec 128} (h : ∀ i < 8, word x i = word y i) : x = y := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have := congrArg (fun w : BitVec 16 => w.getLsbD (j % 16)) (h (j / 16) (by omega_using [hj]))
  simp only [getLsbD_word _ _ _ (show j % 16 < 16 by omega_using []),
    show 16 * (j / 16) + j % 16 = j by omega_using []] at this
  exact this

/-- The words of a doubleword. -/
theorem word_dword (x : BitVec 128) (k : Nat) (e : Nat) (he : e < 2) :
    word x (2 * k + e) = (dword x k).extractLsb' (16 * e) 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [getLsbD_word _ _ _ hj, dword, BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and,
    decide_eq_true (show 16 * e + j < 32 by omega_using [he, hj])]
  congr 1; omega_using []

/-- A word is the word of its doubleword. -/
theorem word_eq_dword (x : BitVec 128) (i : Nat) :
    word x i = (dword x (i / 2)).extractLsb' (16 * (i % 2)) 16 := by
  have := word_dword x (i / 2) (i % 2) (by omega_using [])
  rwa [show 2 * (i / 2) + i % 2 = i by omega_using []] at this

/-- The words of a quadword. -/
theorem word_qword (x : BitVec 128) (k : Nat) (e : Nat) (he : e < 4) :
    word x (4 * k + e) = (qword x k).extractLsb' (16 * e) 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [getLsbD_word _ _ _ hj, qword, BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and,
    decide_eq_true (show 16 * e + j < 64 by omega_using [he, hj])]
  congr 1; omega_using []

/-! ## Loads and stores -/

theorem word_readW (m : Mem) (a : Addr) {j : Nat} (hj : j < 8) :
    word (m.readW a 128) j = m.readW (a + BitVec.ofNat 64 (2 * j)) 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [word, BitVec.getLsbD_extractLsb', Mem.readW, BitVec.getLsbD_setWidth]
  simp only [hi, decide_true, Bool.true_and]
  rw [getLsbD_read _ _ (by omega_using [hj, hi]), getLsbD_read _ _ (by omega_using [hi])]
  rw [show a + BitVec.ofNat 64 ((16 * j + i) / 8) = a + BitVec.ofNat 64 (2 * j) + BitVec.ofNat 64 (i / 8) by
    rw [show (16 * j + i) / 8 = 2 * j + i / 8 by omega_using [], BitVec.ofNat_add, BitVec.add_assoc]]
  simp only [decide_eq_true (show 16 * j + i < 128 by omega_using [hj, hi]), Bool.true_and]
  exact congrArg _ (by omega_using [])

theorem readW_writeW128_16 (m : Mem) (a : Addr) (v : BitVec 128) {j : Nat} (hj : j < 8) :
    (m.writeW a v).readW (a + BitVec.ofNat 64 (2 * j)) 16 = word v j := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [word, BitVec.getLsbD_extractLsb', Mem.readW, BitVec.getLsbD_setWidth, hi, decide_true,
    Bool.true_and]
  rw [getLsbD_read _ _ (by omega_using [hi])]
  simp only [Mem.writeW, Mem.write]
  rw [show a + BitVec.ofNat 64 (2 * j) + BitVec.ofNat 64 (i / 8) - a = BitVec.ofNat 64 (2 * j + i / 8) by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Offset.add_sub_cancel_left]]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hj, hi])]
  simp only [show 2 * j + i / 8 < 128 / 8 by omega_using [hj, hi], ite_true, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_setWidth]
  rw [decide_eq_true (by omega_using []), decide_eq_true (by omega_using [hj, hi]), Bool.true_and, Bool.true_and]
  exact congrArg _ (by omega_using [])

/-! ## The word instructions -/

section
variable (a b : BitVec 128) {i : Nat}

theorem word_paddw (hi : i < 8) : word (XBinOp.eval .paddw a b) i = word a i + word b i := by
  simp only [XBinOp.eval]; exact word_ofWords _ hi

theorem word_psubw (hi : i < 8) : word (XBinOp.eval .psubw a b) i = word a i - word b i := by
  simp only [XBinOp.eval]; exact word_ofWords _ hi

theorem word_pmullw (hi : i < 8) :
    word (pmullw a b) i = (mulWordsSigned (word a i) (word b i)).extractLsb' 0 16 :=
  word_ofWords _ hi

theorem word_pmulhw (hi : i < 8) :
    word (pmulhw a b) i = (mulWordsSigned (word a i) (word b i)).extractLsb' 16 16 :=
  word_ofWords _ hi

theorem word_punpcklwd (hi : i < 8) :
    word (XBinOp.eval .punpcklwd a b) i = if i % 2 = 0 then word a (i / 2) else word b (i / 2) := by
  simp only [XBinOp.eval]; exact word_ofWords _ hi

theorem word_punpckhwd (hi : i < 8) :
    word (XBinOp.eval .punpckhwd a b) i = if i % 2 = 0 then word a (4 + i / 2) else word b (4 + i / 2) := by
  simp only [XBinOp.eval]; exact word_ofWords _ hi

theorem word_packssdw (hi : i < 8) :
    word (XBinOp.eval .packssdw a b) i =
      if i < 4 then satSignedWord (dword a i) else satSignedWord (dword b (i - 4)) := by
  simp only [XBinOp.eval]; exact word_ofWords _ hi

theorem word_psraw (n : BitVec 8) (hi : i < 8) :
    word (XShiftOp.eval .psraw a n) i = (word a i).sshiftRight (min n.toNat 16) := by
  simp only [XShiftOp.eval]; exact word_ofWords _ hi

theorem word_pand : word (XBinOp.eval .pand a b) i = word a i &&& word b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [XBinOp.eval, BitVec.getLsbD_and, getLsbD_word _ _ _ hj]

theorem word_pxor : word (XBinOp.eval .pxor a b) i = word a i ^^^ word b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [XBinOp.eval, BitVec.getLsbD_xor, getLsbD_word _ _ _ hj]

theorem word_movdqa : word (XBinOp.eval .movdqa a b) i = word b i := rfl

theorem word_punpcklqdq (hi : i < 8) :
    word (XBinOp.eval .punpcklqdq a b) i = if i < 4 then word a i else word b (i - 4) := by
  have e : XBinOp.eval .punpcklqdq a b = qword b 0 ++ qword a 0 := rfl
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [getLsbD_word _ _ _ hj, e, BitVec.getLsbD_append]
  by_cases h : i < 4
  · rw [ite_eq_left h, getLsbD_word _ _ _ hj]
    simp only [qword, BitVec.getLsbD_extractLsb', show 16 * i + j < 64 by omega_using [h, hj], decide_true,
      Bool.true_and, ↓reduceIte, Nat.mul_zero, Nat.zero_add]
  · rw [ite_eq_right h, getLsbD_word _ _ _ hj]
    simp only [qword, BitVec.getLsbD_extractLsb', show ¬16 * i + j < 64 by omega_using [h], ↓reduceIte,
      show 16 * i + j - 64 < 64 by omega_using [hi, hj], decide_true, Bool.true_and, Nat.mul_zero, Nat.zero_add]
    congr 1; omega_using [h]

theorem word_punpckhqdq (hi : i < 8) :
    word (XBinOp.eval .punpckhqdq a b) i = if i < 4 then word a (4 + i) else word b i := by
  have e : XBinOp.eval .punpckhqdq a b = qword b 1 ++ qword a 1 := rfl
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [getLsbD_word _ _ _ hj, e, BitVec.getLsbD_append]
  by_cases h : i < 4
  · rw [ite_eq_left h, getLsbD_word _ _ _ hj]
    simp only [qword, BitVec.getLsbD_extractLsb', show 16 * i + j < 64 by omega_using [h, hj], decide_true,
      Bool.true_and, ↓reduceIte, Nat.mul_one]
    congr 1; omega_using []
  · rw [ite_eq_right h, getLsbD_word _ _ _ hj]
    simp only [qword, BitVec.getLsbD_extractLsb', show ¬16 * i + j < 64 by omega_using [h], ↓reduceIte,
      show 16 * i + j - 64 < 64 by omega_using [hi, hj], decide_true, Bool.true_and, Nat.mul_one]
    congr 1; omega_using [h]

end

end VG.X86
