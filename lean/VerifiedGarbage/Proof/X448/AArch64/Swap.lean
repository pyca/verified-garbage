module
public import VerifiedGarbage.Proof.X448.AArch64.Mul

import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset

/-!
# X448 on AArch64: constant-time conditional swaps

An XOR mask exchanges the limbs without a branch or an address depending on
the swap bit.
-/

@[expose] public section

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

def mask (sw : Bool) : BitVec 64 := if sw then BitVec.allOnes 64 else 0

theorem xor_sel (sw : Bool) (a b : BitVec 64) :
    a ^^^ ((a ^^^ b) &&& mask sw) = (if sw then b else a) ∧
      b ^^^ ((a ^^^ b) &&& mask sw) = (if sw then a else b) := by
  cases sw
  · simp only [mask, Bool.false_eq_true, ite_false]
    constructor <;> (apply BitVec.eq_of_toNat_eq; simp)
  · simp only [mask, ite_true, BitVec.and_allOnes]
    constructor
    · rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    · rw [BitVec.xor_comm a b, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- Reading two disjoint words after writing a limb pair. -/
theorem pair_write {m : Mem} {base : Addr} {x y n j : Nat} (hx : Slot x) (hy : Slot y)
    (hxy : x + 128 ≤ y ∨ y + 128 ≤ x) (hn : n < 16) (hj : j < 16) (vx vy : BitVec 64) :
    let m' := (m.writeW (off base (x + 8 * n)) vx).writeW (off base (y + 8 * n)) vy
    limbs m' base x j = (if j = n then vx.toNat else limbs m base x j) ∧
    limbs m' base y j = (if j = n then vy.toNat else limbs m base y j) := by
  have xb : x + 128 ≤ 8192 := Nat.le_trans hx (by decide)
  have yb : y + 128 ≤ 8192 := Nat.le_trans hy (by decide)
  dsimp only
  constructor
  · simp only [limbs, word]
    rw [Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide)]
    rw [show m.readW (off base (x + 8 * j)) 64 = word m base (x + 8 * j) from rfl]
    change (word (m.writeW (off base (x + 8 * n)) vx) base (x + 8 * j)).toNat = _
    rw [word_write m base (by omega) (by omega)]
    split <;> rfl
  · change (word ((m.writeW (off base (x + 8 * n)) vx).writeW (off base (y + 8 * n)) vy)
      base (y + 8 * j)).toNat = _
    rw [word_write (m.writeW (off base (x + 8 * n)) vx) base (by omega) (by omega)]
    by_cases h : j = n
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h]
      apply congrArg BitVec.toNat
      exact Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide)

end VG.Proof.X448.AArch64
