module
public import VerifiedGarbage.TCB.AArch64.Isa

import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import Mathlib.Tactic.SplitIfs
import Mathlib.Util.CompileInductive
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.AArch64.Simd

/-! Loads, stores and byte reversal for pairs of 64-bit lanes. -/

@[expose] public section

namespace VG.AArch64

theorem vdword_read16 (m : Mem) (p : Addr) {e : Nat} (he : e < 2) :
    vdword (m.read p 16) e = m.readW (p + BitVec.ofNat 64 (8 * e)) 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vdword, BitVec.getLsbD_extractLsb', Mem.readW, BitVec.getLsbD_setWidth,
    hi, decide_true, Bool.true_and]
  rw [getLsbD_read m 16 _ (64 * e + i) (by omega), getLsbD_read m 8 _ i (by omega),
    BitVec.add_assoc, ← BitVec.ofNat_add,
    show 8 * e + i / 8 = (64 * e + i) / 8 by omega,
    show (64 * e + i) % 8 = i % 8 by omega]

theorem read16_dwords (m : Mem) (p : Addr) :
    m.read p 16 = ofVDwords (m.readW p 64) (m.readW (p + BitVec.ofNat 64 8) 64) := by
  apply vec64_ext
  · rw [vdword_read16 _ _ (by decide), vdword_ofVDwords_0]; simp
  · rw [vdword_read16 _ _ (by decide), vdword_ofVDwords_1]

/-- `WriteBytes.writeBytes_append`, at an offset given as a literal. -/
private theorem writeBytes_append_at (m : Mem) (q : Addr) (xs ys : List Byte) (k : Nat)
    (hk : xs.length = k) (h : k + ys.length < 2 ^ 64) :
    WriteBytes.writeBytes (WriteBytes.writeBytes m q xs) (q + BitVec.ofNat 64 k) ys =
      WriteBytes.writeBytes m q (xs ++ ys) := by
  subst hk; exact WriteBytes.writeBytes_append m q xs ys h

theorem write16_dwords (m : Mem) (p : Addr) (a b : BitVec 64) :
    m.write p 16 (ofVDwords a b) = (m.writeW p a).writeW (p + BitVec.ofNat 64 8) b := by
  simp only [Mem.writeW, WriteBytes.write_eq_writeBytes]
  rw [writeBytes_append_at _ _ _ _ 8 (by simp only [List.length_map, List.length_range]) (by simp)]
  refine congrArg (WriteBytes.writeBytes m p) ?_
  simp (disch := decide) only [List.range, List.range.loop, List.map, List.cons_append,
    List.nil_append,
    ofVDwords, BitVec.extractLsb'_append_eq_of_add_le, BitVec.extractLsb'_append_eq_of_le,
    Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.setWidth_eq]

theorem getLsbD_rev64 (x : BitVec 64) {i : Nat} (hi : i < 64) :
    (rev64 x).getLsbD i = x.getLsbD (8 * (7 - i / 8) + i % 8) := by
  obtain ⟨a, b, hb, rfl⟩ : ∃ a b, b < 8 ∧ i = 8 * a + b :=
    ⟨i / 8, i % 8, Nat.mod_lt _ (by decide), (Nat.div_add_mod i 8).symm⟩
  have ha : a < 8 := by omega
  rw [show (8 * a + b) / 8 = a by omega, show (8 * a + b) % 8 = b by omega]
  unfold rev64
  -- The byte's index is a literal: each `if` and subtraction reduces without `omega`.
  match a, ha with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp only [getLsbD_append_block _ _ _ hb, Nat.reduceSub, Nat.reduceEqDiff, ↓reduceIte]
    simp only [BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and, Nat.reduceMul, Nat.zero_add]

theorem vdword_rev64b (x : BitVec 128) {e : Nat} (he : e < 2) :
    vdword (VRevOp.rev64b.eval x) e = rev64 (vdword x e) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vdword, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, VRevOp.eval]
  rw [show 64 * e + i = 8 * (8 * e + i / 8) + i % 8 by omega,
    getLsbD_ofVBytes _ (by omega) (by omega), getLsbD_rev64 _ hi]
  simp only [vbyte, BitVec.getLsbD_extractLsb', show i % 8 < 8 by omega,
    show 8 * (7 - i / 8) + i % 8 < 64 by omega, decide_true, Bool.true_and]
  exact congrArg x.getLsbD (by omega)

end VG.AArch64
