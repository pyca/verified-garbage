module

public import VerifiedGarbage.Proof.Framework.Mem
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # A shorter native read contains the low bytes of an RSA array -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG

theorem read_prefix (m : Mem) (a : Addr) {n k : Nat} (hk : k ≤ n) :
    m.read a k = (m.read a n).setWidth (8 * k) := by
  apply Mem.read_eq_of_bytes
  intro j hj
  rw [← Mem.extractLsb'_read m a (n := n) (by omega)]
  ext i hi
  simp only [BitVec.getElem_extractLsb']
  rw [BitVec.getLsbD_setWidth, decide_eq_true (by omega : 8 * j + i < 8 * k), Bool.true_and]

theorem read_prefix_value (m : Mem) (a : Addr) {n k : Nat} (hk : k ≤ n)
    (fit : (m.read a n).toNat < 2 ^ (8 * k)) :
    (m.read a k).toNat = (m.read a n).toNat := by
  rw [read_prefix m a hk, BitVec.toNat_setWidth, Nat.mod_eq_of_lt fit]

end VG.Proof.Bignum.Arm
