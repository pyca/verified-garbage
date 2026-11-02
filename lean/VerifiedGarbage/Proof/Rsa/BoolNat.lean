module

public import VerifiedGarbage.Proof.Rsa.TwosMath
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Bignum.Math

/-!
# Booleans as naturals

`b2n b`: 1 if `b`, else 0.
-/

@[expose] public section

namespace VG.Proof.Rsa

open VG.Proof.Bignum (mont_cancel)

/-- A Boolean as a word. -/
def b2n (b : Bool) : Nat := if b then 1 else 0

theorem b2n_le (b : Bool) : b2n b ≤ 1 := by cases b <;> decide

end VG.Proof.Rsa
