module

import VerifiedGarbage.Proof.Bignum.Arm.MontMath
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Final reduction on the packed-word representation -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Proof.Mont

theorem val32_top2 (mem : Mem) (base : Addr) (a n : Nat) :
    val32 mem base a (n + 2) = val32 mem base a n + 2 ^ (32 * n) *
      (w32 mem base (a + 4 * n) + 2 ^ 32 * w32 mem base (a + 4 * n + 4)) := by
  rw [val32_append mem base a n 2, val32, val32, val32, Nat.mul_zero, Nat.add_zero]

theorem csub_value {mem mem' : Mem} {base : Addr} {acc mod tmp n borrow : Nat}
    (hb : borrow ≤ 1)
    (hT : val32 mem base acc (n + 2) < 2 * val32 mem base mod n)
    (hsub : val32 mem' base tmp n + val32 mem base mod n =
      val32 mem base acc n + 2 ^ (32 * n) * borrow) :
    (if borrow ≤ w32 mem base (acc + 4 * n) then val32 mem' base tmp n else val32 mem base acc n) =
      val32 mem base acc (n + 2) % val32 mem base mod n := by
  rw [val32_top2] at hT ⊢
  have h := csub_result (val32_lt mem base mod n) (val32_lt mem' base tmp n) hb
    (val32_lt mem base acc n) hT hsub
  by_cases hc : borrow ≤ w32 mem base (acc + 4 * n)
  · simpa only [hc, Nat.not_lt.mpr hc, ite_true, ite_false] using h
  · have hlt : w32 mem base (acc + 4 * n) < borrow := by omega
    simpa only [hc, hlt, ite_true, ite_false] using h

end VG.Proof.Bignum.Arm
