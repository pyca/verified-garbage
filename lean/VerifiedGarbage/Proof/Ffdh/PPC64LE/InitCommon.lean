module

import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.Framework.PPC64LE.Run
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Ffdh.ControlMemory
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-! # The FFDH controllers' initialization on PPC64LE: shared lemmas

The comparisons by the sign bit of a difference (`lt_bit`), the high bits of
a width (`shr_zero`), and the four public words the initializations write
(`initWritten`), at offsets of a 128-byte state the code may write (`st`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE

open VG VG.PPC64LE VG.Proof.Bignum

/-- The sign bit of `n − c`, for `n` and `c` below `2^63`, is `n < c`. -/
theorem lt_bit {n c : Nat} (hn : n < 2 ^ 63) (hc : c < 2 ^ 63) :
    (BitVec.ofNat 64 n - BitVec.ofNat 64 c) >>> 63 = BitVec.ofNat 64 (if n < c then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  split <;> omega

/-- `n >> k` is zero exactly when `n < 2^k`. -/
theorem shr_zero {n k : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n >>> k == 0) = decide (n < 2 ^ k) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt hn] at this
    exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos k)).mp this
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt hn]
    exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos k)).mpr h

/-- The four public words written. -/
def initWritten (m : Mem) (B : Addr) (a b c d : BitVec 64) : Mem :=
  (((m.writeW B a).writeW (off B 8) b).writeW (off B 16) c).writeW (off B 24) d

theorem initWritten_words (m : Mem) (B : Addr) (a b c d : BitVec 64) :
    Spec.Rsa.wordsAt (initWritten m B a b c d) B 4 = [a, b, c, d] := by
  change [word (initWritten m B a b c d) B (8 * 0), word (initWritten m B a b c d) B (8 * 1),
    word (initWritten m B a b c d) B (8 * 2), word (initWritten m B a b c d) B (8 * 3)] = _
  have hm : initWritten m B a b c d =
      (((m.writeW (off B (8 * 0)) a).writeW (off B (8 * 1)) b).writeW (off B (8 * 2)) c).writeW
        (off B (8 * 3)) d := by
    simp only [initWritten, off, Nat.mul_zero, BitVec.add_zero]
  rw [hm]
  simp only [Control.controller_store_word _ _ _ (i := 3) (by decide) (by decide : (0 : Nat) < 16),
    Control.controller_store_word _ _ _ (i := 3) (by decide) (by decide : (1 : Nat) < 16),
    Control.controller_store_word _ _ _ (i := 3) (by decide) (by decide : (2 : Nat) < 16),
    Control.controller_store_word _ _ _ (i := 3) (by decide) (by decide : (3 : Nat) < 16),
    Control.controller_store_word _ _ _ (i := 2) (by decide) (by decide : (0 : Nat) < 16),
    Control.controller_store_word _ _ _ (i := 2) (by decide) (by decide : (1 : Nat) < 16),
    Control.controller_store_word _ _ _ (i := 2) (by decide) (by decide : (2 : Nat) < 16),
    Control.controller_store_word _ _ _ (i := 1) (by decide) (by decide : (0 : Nat) < 16),
    Control.controller_store_word _ _ _ (i := 1) (by decide) (by decide : (1 : Nat) < 16),
    Control.controller_store_word _ _ _ (i := 0) (by decide) (by decide : (0 : Nat) < 16),
    Nat.reduceEqDiff, ite_true, ite_false]

/-- The state's 128 bytes, the only region the code may write. -/
def StateWr (s : State) : Prop :=
  s.wr = [⟨s.gpr .r3, 128⟩] ∧ (s.gpr .r3).toNat + 128 ≤ 2 ^ 64

theorem st {s : State} (h : StateWr s) (d : Nat) (hd : d + 8 ≤ 128) :
    InRegions s.wr (s.gpr .r3 + BitVec.ofNat 64 d) 8 := by
  rw [h.1]
  exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ hd (by omega)⟩

theorem st0 {s : State} (h : StateWr s) : InRegions s.wr (s.gpr .r3) 8 := by
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using st h 0 (by decide)

end VG.Proof.Ffdh.PPC64LE
