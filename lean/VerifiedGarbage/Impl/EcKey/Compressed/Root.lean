module

public import VerifiedGarbage.Spec.Weierstrass

/-!
# Public square-root algorithms for compressed points

The functional algorithms used in the proofs of coordinate recovery. The
three-mod-four case uses one fixed exponent. P-224 uses the two-adic
descent with `p - 1 = q * 2^s`, odd `q`, and a quadratic nonresidue `z`.
The descent has exactly `s - 1` rounds; all its inputs are public.
-/

@[expose] public section

namespace VG.Impl.EcKey.Compressed

open Spec.Weierstrass

variable {p : Nat} [NeZero p]

/-- A square-root candidate for a prime congruent to three modulo four. -/
def rootThreeModFour (a : Fin p) : Fin p := pow a ((p + 1) / 4)

/-- Remove one power of two from the order of `t` per round, maintaining
`r² = a t`. The initial `c` has order `2^s`. -/
def rootDescent : Nat → Fin p → Fin p → Fin p → Fin p
  | 0, r, _, _ => r
  | n + 1, r, t, c =>
    let b := if pow t (2 ^ n) = 1 then 1 else c
    rootDescent n (r * b) (t * (b * b)) (c * c)

/-- A square-root candidate for an odd prime congruent to one modulo four.
The caller checks its square and requested parity before accepting it. -/
def rootTonelli (a : Fin p) (q s : Nat) (z : Fin p) : Fin p :=
  if a = 0 then 0 else
    rootDescent (s - 1) (pow a ((q + 1) / 2)) (pow a q) (pow z q)

/-- Choose a root with the requested canonical parity when possible. -/
def chooseRoot (y : Fin p) (parity : Nat) : Fin p :=
  if y.val % 2 = parity then y else -y

/-- Check both the square and parity, rejecting an odd encoding of zero. -/
def recoverRoot (root : Fin p → Fin p) (a : Fin p) (parity : Nat) : Option (Fin p) :=
  let y := root a
  let y := if y.val % 2 = parity then y else -y
  if y * y = a ∧ y.val % 2 = parity then some y else none

end VG.Impl.EcKey.Compressed
