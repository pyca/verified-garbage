module

public import VerifiedGarbage.Spec.X25519
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.Ring

-- separate module: the identities are checked without the vector code, which changes apart from them.

/-!
# The arithmetic of the squares modulo 2²⁵⁵ - 19

Untrusted: everything here is checked by Lean. The limbs `l k` (low) and `h k`
(high) of an element are at bits `51 k` and `51 k + 26`.
-/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Squares

open VG.Spec.X25519 (P)

/-- The element of the limbs `l k` and `h k`. -/
def limbs (l0 h0 l1 h1 l2 h2 l3 h3 l4 h4 : Nat) : Nat :=
  (l0 + 2 ^ 26 * h0) + 2 ^ 51 * (l1 + 2 ^ 26 * h1) + 2 ^ 102 * (l2 + 2 ^ 26 * h2) + 2 ^ 153 * (l3 + 2 ^ 26 * h3) +
    2 ^ 204 * (l4 + 2 ^ 26 * h4)

/-- The value of the columns. -/
def colVal (e0 c0 e1 c1 e2 c2 e3 c3 e4 c4 : Nat) : Nat := limbs e0 c0 e1 c1 e2 c2 e3 c3 e4 c4

/-- A square's columns. -/
theorem columns_value (l0 h0 l1 h1 l2 h2 l3 h3 l4 h4 : Nat) :
    colVal
      (2 * (2 * h0 * (19 * h4) + 2 * h1 * (19 * h3) + h2 * (19 * h2)) + (l0 * l0 + 2 * l1 * (19 * l4) + 2 * l2 * (19 * l3)))
      (2 * h0 * l0 + 2 * h1 * (19 * l4) + 2 * l1 * (19 * h4) + 2 * h2 * (19 * l3) + 2 * l2 * (19 * h3))
      (2 * (h0 * h0 + 2 * h1 * (19 * h4) + 2 * h2 * (19 * h3)) + (2 * l0 * l1 + 2 * l2 * (19 * l4) + l3 * (19 * l3)))
      (2 * h0 * l1 + 2 * l0 * h1 + 2 * h2 * (19 * l4) + 2 * l2 * (19 * h4) + 2 * h3 * (19 * l3))
      (2 * (2 * h0 * h1 + 2 * h2 * (19 * h4) + h3 * (19 * h3)) + (2 * l0 * l2 + l1 * l1 + 2 * l3 * (19 * l4)))
      (2 * h0 * l2 + 2 * l0 * h2 + 2 * h1 * l1 + 2 * h3 * (19 * l4) + 2 * l3 * (19 * h4))
      (2 * (2 * h0 * h2 + h1 * h1 + 2 * h3 * (19 * h4)) + (2 * l0 * l3 + 2 * l1 * l2 + l4 * (19 * l4)))
      (2 * h0 * l3 + 2 * l0 * h3 + 2 * h1 * l2 + 2 * l1 * h2 + 2 * h4 * (19 * l4))
      (2 * (2 * h0 * h3 + 2 * h1 * h2 + h4 * (19 * h4)) + (2 * l0 * l4 + 2 * l1 * l3 + l2 * l2))
      (2 * h0 * l4 + 2 * l0 * h4 + 2 * h1 * l3 + 2 * l1 * h3 + 2 * h2 * l2) % P =
    limbs l0 h0 l1 h1 l2 h2 l3 h3 l4 h4 * limbs l0 h0 l1 h1 l2 h2 l3 h3 l4 h4 % P := by
  rw [← Nat.add_mul_mod_self_left _ P (
      2 ^ 1 * (2 * h0 * h4) + 2 ^ 1 * (2 * h1 * h3) + 2 ^ 0 * (2 * l1 * l4) + 2 ^ 26 * (2 * l1 * h4 + 2 * h1 *
        l4) + 2 ^ 52 * (2 * h1 * h4) + 2 ^ 1 * (h2 * h2) + 2 ^ 0 * (2 * l2 * l3) + 2 ^ 26 * (2 * l2 * h3 + 2 *
        h2 * l3) + 2 ^ 52 * (2 * h2 * h3) + 2 ^ 51 * (2 * l2 * l4) + 2 ^ 77 * (2 * l2 * h4 + 2 * h2 * l4) + 2 ^
        103 * (2 * h2 * h4) + 2 ^ 51 * (l3 * l3) + 2 ^ 77 * (2 * l3 * h3) + 2 ^ 103 * (h3 * h3) + 2 ^ 102 * (2 *
        l3 * l4) + 2 ^ 128 * (2 * l3 * h4 + 2 * h3 * l4) + 2 ^ 154 * (2 * h3 * h4) + 2 ^ 153 * (l4 * l4) + 2 ^
        179 * (2 * l4 * h4) + 2 ^ 205 * (h4 * h4))]
  refine congrArg (· % P) ?_
  simp only [colVal, limbs, P]
  ring

end VG.Proof.X25519.AArch64.Squares
