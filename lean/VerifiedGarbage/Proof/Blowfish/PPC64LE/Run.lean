module

import VerifiedGarbage.Impl.Blowfish.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Run
public meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Blowfish
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# Blowfish on PPC64LE: running blocks

`brun [facts]` runs a block of the Blowfish code symbolically (`crun`),
keeping 32-bit loads and doubleword stores as `Mem.readW` and `Mem.writeW`
and byte loads as the byte, as IDEA's `irun` (`Proof/Idea/PPC64LE/Round.lean`).
The code's 32-bit values live in the low words of registers: `lo` is that
word, and the `lo_*` lemmas take it through the operations the code uses.
-/

@[expose] public section

namespace VG.Proof.Blowfish.PPC64LE

open VG VG.PPC64LE VG.Impl.Blowfish.PPC64LE

theorem read_one (m : Mem) (a : Addr) : (m.read a 1 : BitVec 8) = m a := by
  simp only [Mem.read]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append]
  simp

theorem read_four (m : Mem) (a : Addr) : m.read a 4 = m.readW a 32 := by
  simp only [Mem.readW, BitVec.setWidth_eq]

theorem read_eight (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by
  simp only [Mem.readW, BitVec.setWidth_eq]

theorem write_eight (m : Mem) (a : Addr) (v : BitVec 64) : m.write a 8 v = m.writeW a v := by
  simp only [Mem.writeW, BitVec.setWidth_eq]

theorem write_four (m : Mem) (a : Addr) (v : BitVec 32) : m.write a 4 v = m.writeW a v := by
  simp only [Mem.writeW, BitVec.setWidth_eq]

/-- Steps a block of the Blowfish code. -/
syntax "brun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| brun) => `(tactic| brun [])
  | `(tactic| brun [$ls,*]) => `(tactic|
      crun [List.cons_append, List.nil_append, ↓read_one, ↓read_four, ↓read_eight, write_eight,
        write_four, false_implies, zero, sch, xL, xR, fReg, pPtr, qReg, acc, mReg, tmp, lane, rowPtr,
        ptr, cnt, $ls,*])

theorem WP.reassoc {a b c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a b) c) s Q) : WP isa (.seq a (.seq b c)) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp h)) fun _ h => WP.seq h)

/-! ## Low words -/

/-- The low word of a register. -/
abbrev lo (x : BitVec 64) : BitVec 32 := x.setWidth 32

theorem lo_and (x y : BitVec 64) : lo (x &&& y) = lo x &&& lo y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

theorem lo_or (x y : BitVec 64) : lo (x ||| y) = lo x ||| lo y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

theorem lo_xor (x y : BitVec 64) : lo (x ^^^ y) = lo x ^^^ lo y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

theorem lo_add (x y : BitVec 64) : lo (x + y) = lo x + lo y := lo32_add x y

theorem lo_ext (x : BitVec 32) : lo (x.setWidth 64) = x := lo32_ext x

theorem lo_ofNat (n : Nat) : lo (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_mod_of_dvd _ (by decide)]

/-- Whether bit `c` of `q` is set, as the mask `0 - ((q << (63 - c)) >> 63)`. -/
theorem bitMask_eq (q : BitVec 64) {c : Nat} (hc : c < 64) :
    0#64 - (q <<< (63 - c)) >>> 63 = if q.getLsbD c then BitVec.allOnes 64 else 0 := by
  have e : (q <<< (63 - c)) >>> 63 = if q.getLsbD c then 1#64 else 0#64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    by_cases h0 : i = 0
    · subst h0
      simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
        show (63 : Nat) < 64 by decide, decide_true, Bool.true_and,
        show ¬ (63 < 63 - c) by omega, decide_false, Bool.not_false,
        show 63 - (63 - c) = c by omega]
      cases q.getLsbD c <;> rfl
    · have : (q <<< (63 - c) >>> 63).getLsbD i = false := by
        simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
        simp only [show ¬ (63 + i < 64) by omega, decide_false, Bool.false_and]
      rw [this]
      cases q.getLsbD c
      · simp
      · simp [h0]
  rw [e]
  cases q.getLsbD c <;> decide

/-- `x XOR ((r XOR x) AND m)` for an all-ones-or-zero mask. -/
theorem select_eq (x r : BitVec 64) (b : Bool) :
    x ^^^ ((r ^^^ x) &&& (if b then BitVec.allOnes 64 else 0)) = if b then r else x := by
  cases b
  · simp
  · simp only [ite_true, BitVec.and_allOnes]
    rw [BitVec.xor_comm r x, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- `0 - ((v - 1) >> 63)` is all ones exactly when `v < 2 ^ 63` is zero. -/
theorem isZero_eq (v : BitVec 64) (h : v.toNat < 2 ^ 63) :
    0#64 - (v - 1#64) >>> 63 = if v.toNat = 0 then BitVec.allOnes 64 else 0 := by
  by_cases e : v.toNat = 0
  · have : v = 0#64 := BitVec.eq_of_toNat_eq (by simp [e])
    subst this; decide
  · rw [ite_eq_right e]
    have : (v - 1#64) >>> 63 = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub]
      simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      omega
    rw [this]; rfl

end VG.Proof.Blowfish.PPC64LE
