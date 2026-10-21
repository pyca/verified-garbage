module

import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
import Mathlib.Tactic.Ring
public import VerifiedGarbage.Spec.Rsa.FixedBaseComb

/-! The low-bit subset recurrence used by a compact comb-table builder.
The finite index arithmetic is independent of modulus, base and word width. -/

@[expose] public section
namespace VG.Proof.Rsa.FixedBaseComb
open VG.Spec.Rsa.FixedBaseComb (exponent)

/-- Isolate the least set bit using the same 32-bit operations as the code. -/
def lowTooth (a : Nat) : Nat :=
  ((0 - BitVec.ofNat 32 a) &&& BitVec.ofNat 32 a).toNat

private theorem lowTooth_coeff : ∀ a < 32, ∀ j < 5,
    a / 2^j % 2 = (a - lowTooth a) / 2^j % 2 + lowTooth a / 2^j % 2 := by
  decide

/-- Both input table entries precede the current entry, except the already
initialized single-tooth entry. The zero entry supplies Montgomery one. -/
theorem lowTooth_bounds : ∀ a < 32, 0 < a →
    0 < lowTooth a ∧ lowTooth a ≤ a ∧ a - lowTooth a < a ∧
    (lowTooth a = 1 ∨ lowTooth a = 2 ∨ lowTooth a = 4 ∨
      lowTooth a = 8 ∨ lowTooth a = 16) := by
  decide

/-- Multiplying the low-tooth entry by the remaining-subset entry gives
exactly the existing RSA comb table exponent. -/
theorem exponent_lowTooth (bits a : Nat) (ha : a < 32) :
    exponent bits a = exponent bits (a - lowTooth a) + exponent bits (lowTooth a) := by
  simp only [exponent, VG.Spec.Rsa.FixedBaseComb.teeth, List.range_succ, List.range_zero,
    List.map_append, List.map_cons, List.map_nil, List.foldl_append, List.foldl_cons,
    List.foldl_nil]
  rw [lowTooth_coeff a ha 0 (by decide), lowTooth_coeff a ha 1 (by decide),
    lowTooth_coeff a ha 2 (by decide), lowTooth_coeff a ha 3 (by decide),
    lowTooth_coeff a ha 4 (by decide)]
  ring

end VG.Proof.Rsa.FixedBaseComb
