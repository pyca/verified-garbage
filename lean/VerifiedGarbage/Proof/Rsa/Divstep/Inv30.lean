module

public import VerifiedGarbage.Proof.Rsa.Divstep.Inv30Def
import VerifiedGarbage.Proof.Divstep.Red30
import VerifiedGarbage.Proof.Rsa.Divstep.InvBounds
import VerifiedGarbage.Proof.Rsa.Divstep.InvResult
import Mathlib.Algebra.Order.Ring.Int
-- separate module: target-independent, for any target's batched inverse

/-! # The inverse from batches of 30 divsteps with coefficients reduced by `2^30`

`inv30 n a m`: after the `3 (n + 1)` batches that finish for `a, m < 2^(32 n)`
(`invRun_done`), the coefficient `d` of `f` with `f`'s sign, modulo `m`: `x < m` with
`x a ≡ gcd(a, m) (mod m)` for odd `m > 1` (`inv30_spec`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Divstep
open VG.Proof.Divstep

theorem inv30_spec {n a m : Nat} (hm : m % 2 = 1) (h1 : 1 < m) (ha : a < 2 ^ (32 * n))
    (hmn : m < 2 ^ (32 * n)) :
    (m : Int) ∣ (inv30 n a m : Int) * a - Nat.gcd a m ∧ inv30 n a m < m := by
  have hm0 : (0 : Int) < m := Int.natCast_pos.mpr (by omega)
  set X := oddInput m a
  set f := (W32.invRun 30 m 0 X (3 * (n + 1))).f
  set D := ((W32.deRun m X (3 * (n + 1))).1 : Int)
  have done := invRun_done (inv := 0) hm hmn ha
  have hgcd : f.natAbs = Nat.gcd a m := by rw [Nat.gcd_comm]; exact done.2
  have cf := (W32.deRun_cong (x := X) hm h1 (3 * (n + 1))).1
  set y := (if f < 0 then -D else D) % (m : Int)
  have nn : 0 ≤ y := Int.emod_nonneg _ hm0.ne'
  have lt : y < m := Int.emod_lt_of_pos _ hm0
  have ey : ((inv30 n a m : Nat) : Int) = y := Int.toNat_of_nonneg nn
  refine ⟨?_, by omega⟩
  rw [ey, ← hgcd, Int.natCast_natAbs]
  refine Int.ModEq.dvd ?_
  have e : y * a ≡ (if f < 0 then -D else D) * X [ZMOD m] :=
    Int.ModEq.mul (Int.mod_modEq _ _) (oddInput_cong' m a).symm
  refine Int.ModEq.trans ?_ e.symm
  by_cases hneg : f < 0
  · simp only [hneg, ↓reduceIte, abs_of_neg hneg]
    have := cf.neg
    rwa [neg_mul, Int.mul_comm]
  · simp only [hneg, ↓reduceIte, abs_of_nonneg (not_lt.mp hneg)]
    rw [Int.mul_comm]; exact cf

end VG.Proof.Rsa.Divstep
