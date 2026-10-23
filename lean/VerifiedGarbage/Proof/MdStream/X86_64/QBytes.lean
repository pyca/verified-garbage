module

public import VerifiedGarbage.TCB.X86_64.Sse

/-!
# The bytes of 64-bit words, shifted, and moved into SSE registers

What the one-shot digest's last 16 bytes of message and `0x80`
(`Impl.MdStream.X86_64.OneShot.partLo`, `partHi`) are made of: a word's
bytes after a right shift by whole bytes (`qbyte_shr`), `0x80` shifted to a
byte (`qbyte_mark`), and two words moved into an SSE register (`byte_movq`,
`byte_punpcklqdq`).
-/

@[expose] public section

namespace VG.Proof.MdStream.X86_64

open VG VG.X86_64

/-- Byte `i` of a 64-bit word, little-endian. -/
abbrev qbyte (x : BitVec 64) (i : Nat) : Byte := x.extractLsb' (8 * i) 8

/-- Shifting right by `k` bytes moves byte `i + k` to byte `i`. -/
theorem qbyte_shr (x : BitVec 64) (k i : Nat) :
    qbyte (x >>> (8 * k)) i = if i + k < 8 then qbyte x (i + k) else 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  by_cases h : i + k < 8
  · simp only [h, ite_true, qbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, hj, decide_true,
      Bool.true_and]
    rw [show 8 * k + (8 * i + j) = 8 * (i + k) + j by omega]
  · simp only [h, ite_false, qbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, hj, decide_true,
      Bool.true_and]
    rw [BitVec.getLsbD_of_ge x _ (by omega)]
    simp

theorem qbyte_or (a b : BitVec 64) (i : Nat) : qbyte (a ||| b) i = qbyte a i ||| qbyte b i :=
  BitVec.extractLsb'_or

theorem qbyte_zero (i : Nat) : qbyte 0 i = 0 := BitVec.extractLsb'_zero

/-- `0x80` shifted left by `r` bytes is byte `r`, and the others zeros. -/
theorem qbyte_mark : ∀ r < 8, ∀ i < 8,
    qbyte (BitVec.ofNat 64 0x80 <<< (8 * r)) i = if i = r then 0x80 else 0 := by
  decide

/-- A word moved into an SSE register (`movq`): its bytes, then zeros. -/
theorem byte_movq (x : BitVec 64) (i : Nat) :
    byte ((0 : BitVec 64) ++ x) i = if i < 8 then qbyte x i else 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  by_cases h : i < 8
  · simp only [h, ite_true, byte, qbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hj, decide_true,
      Bool.true_and, show 8 * i + j < 64 by omega]
  · simp only [h, ite_false, byte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hj, decide_true,
      Bool.true_and, show ¬ 8 * i + j < 64 by omega]
    simp

/-- Two words moved into SSE registers, interleaved (`punpcklqdq`): the
first's bytes, then the second's. -/
theorem byte_punpcklqdq (a b : BitVec 64) (i : Nat) :
    byte (XBinOp.eval .punpcklqdq ((0 : BitVec 64) ++ a) ((0 : BitVec 64) ++ b)) i =
      if i < 8 then qbyte a i else qbyte b (i - 8) := by
  have e : ∀ x : BitVec 64, qword ((0 : BitVec 64) ++ x) 0 = x := fun x => by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, Nat.mul_zero, Nat.zero_add, hj,
      decide_true, Bool.true_and, ite_true]
  rw [show XBinOp.eval .punpcklqdq ((0 : BitVec 64) ++ a) ((0 : BitVec 64) ++ b) = b ++ a by
    simp only [XBinOp.eval, e]]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  by_cases h : i < 8
  · simp only [h, ite_true, byte, qbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hj, decide_true,
      Bool.true_and, show 8 * i + j < 64 by omega]
  · simp only [h, ite_false, byte, qbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hj, decide_true,
      Bool.true_and, show ¬ 8 * i + j < 64 by omega]
    rw [show 8 * i + j - 64 = 8 * (i - 8) + j by omega]

end VG.Proof.MdStream.X86_64
