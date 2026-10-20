module
public import VerifiedGarbage.Proof.Bignum.Words

import Mathlib.Tactic.Finiteness.Attr
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.TCB.X86_64.State

/-! # The shared oddness mask for DSA moduli -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64
open VG.Proof.Bignum

theorem word_low_bit (x : BitVec 64) : x &&& 1 = BitVec.ofNat 64 (x.toNat % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show x.toNat % 2 < 2 ^ 64 by omega)]

theorem word_odd_mask (x : BitVec 64) : 0 - (x &&& 1) = mask (decide (x.toNat % 2 = 1)) := by
  rw [word_low_bit]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h <;> rw [h] <;> decide

/-- The implementation combines low bits before converting the result to a mask. -/
theorem modulus_odd_mask (p q : Byte) :
    0 - (p.zeroExtend 64 &&& q.zeroExtend 64 &&& 1) =
      mask (decide (p.toNat % 2 = 1 ∧ q.toNat % 2 = 1)) := by
  rw [word_odd_mask, BitVec.toNat_and]
  change mask (decide (((p.setWidth 64).toNat &&& (q.setWidth 64).toNat) % 2 = 1)) = _
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_trans p.isLt (show 2 ^ 8 < 2 ^ 64 by decide)),
    Nat.mod_eq_of_lt (Nat.lt_trans q.isLt (show 2 ^ 8 < 2 ^ 64 by decide))]
  exact congrArg mask (decide_eq_decide.mpr Nat.and_mod_two_eq_one)

end VG.Proof.Dsa.X86_64
