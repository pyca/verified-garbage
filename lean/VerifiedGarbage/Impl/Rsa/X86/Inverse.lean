module

public import VerifiedGarbage.Impl.Rsa.X86.KeyWs

/-! # The inverse modulo an odd number, on i686: its arrays

The inverse is `32 w` iterations of two steps of the binary extended Euclidean
algorithm modulo the odd `m = [aM]` (`Proof/Rsa/KeyMath.lean`'s `invStep`),
on `(u, v, x₁, x₂)` in arrays 0–3, the first step writing them to arrays 4–7
and the second back, so that no array is copied. From `(a, m, 1, 0)` with
`a, m < 2^(32 w)`, `v` ends as `gcd(a, m)` and `x₂ a ≡ v (mod m)`.

Each step, with `odd` the low bit of `u` and `c` the borrow of `u - v` (`u < v`)
and'ed with it, from the arrays of one bank to the other's:
`v' = c ? u : v`, `u' = (odd ? (c ? v - u : u - v) : u) / 2`,
`x₂' = c ? x₁ : x₂` and `x₁' = halfMod (odd ? (c ? x₂ - x₁ : x₁ - x₂) : x₁)`,
the differences of `x₁` and `x₂` modulo `m`. A difference modulo `m` is the
difference less `[aNM] = 2^(32 w) - m` (the negated modulus) if it borrowed,
and `halfMod x` is `(x - (x odd ? [aNM] : 0) + c' 2^(32 w)) / 2`, `c'` the
low bit of `x` xor'ed with the borrow, which is `(x + m) / 2` if `x` is odd.
Every choice is a masked selection (`sel`), so the addresses and branches
depend only on `w`.
-/

@[expose] public section

namespace VG.Impl.Rsa.X86.Keys
open VG VG.X86 VG.Impl.Mont.X86

/-- The arrays: the two banks of `(u, v, x₁, x₂)` (0–3 and 4–7), `m`, the
negated modulus `2^(32 w) - m`, zero, and four temporaries. -/
def aM : Nat := 8
def aNM : Nat := 9
def aZero : Nat := 10
def aT1 : Nat := 11
def aT2 : Nat := 12
def aT3 : Nat := 13
def aT4 : Nat := 14

end VG.Impl.Rsa.X86.Keys
