module
public import VerifiedGarbage.Proof.Mont.Words

import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The low half of a double-width integer -/

@[expose] public section
namespace VG.Proof.Bignum
open VG VG.Proof.Mont

theorem wordsVal_low_half (m : Mem) (base : Addr) (d n : Nat) :
    wordsVal m base d n = wordsVal m base d (2 * n) % 2 ^ (64 * n) := by
  rw [wordsVal_eq_val32, wordsVal_eq_val32,
    show 2 * (2 * n) = 2 * n + 2 * n by omega, val32_append,
    show 64 * n = 32 * (2 * n) by omega, Nat.add_mod, Nat.mul_mod_right,
    Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt (val32_lt _ _ _ _)]

end VG.Proof.Bignum
