module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.KeyWs

/-!
# The inverse modulo an odd number, on PPC64LE

`inverse`: as on ARMv7 (`Impl/Rsa/Arm/Inverse.lean`), `32 w` iterations of
two steps of the binary extended Euclidean algorithm modulo the odd
`m = [aM]` (`Proof/Rsa/KeyMath.lean`'s `invStep`), on `(u, v, x₁, x₂)` in
arrays 0–3, the first step writing them to arrays 4–7 and the second back,
so that no array is copied. From `(a, m, 1, 0)` with `a, m < 2^(32 w)`, `v`
ends as `gcd(a, m)` and `x₂ a ≡ v (mod m)`.

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

namespace VG.Impl.Rsa.PPC64LE.Keys

open VG.PPC64LE

/-- The arrays: the two banks of `(u, v, x₁, x₂)` (0–3 and 4–7), `m`, the
negated modulus `2^(32 w) - m`, zero, and four temporaries. -/
def aM : Nat := 8
def aNM : Nat := 9
def aZero : Nat := 10
def aT1 : Nat := 11
def aT2 : Nat := 12
def aT3 : Nat := 13
def aT4 : Nat := 14

/-- `[o] := [a] - [b] mod m` for `[a], [b] < m`, through `aT1` and `aT4`. -/
def subModP (o a b : Nat) : List (Prog isa) :=
  [sub3 aT1 a b, .block (stBorrow sB), sel aT4 aZero aNM sB, sub3 o aT1 aT4]

/-- One step from the bank at `A` to the bank at `B`. -/
def invStep (A B : Nat) : Prog isa := seqs ([
  .block (bitOf sOdd A),
  sub3 aT1 A (A + 1),
  .block (stBorrow sB ++ andS sC sOdd sB),
  sub3 aT2 (A + 1) A,
  sel (B + 1) (A + 1) A sC,
  sel aT3 aT1 aT2 sC,
  sel B A aT3 sOdd,
  .block [.li .r9 0],
  half B] ++
  subModP aT3 (A + 2) (A + 3) ++ subModP aT2 (A + 3) (A + 2) ++ [
  sel (B + 3) (A + 3) (A + 2) sC,
  sel aT1 aT3 aT2 sC,
  sel aT3 (A + 2) aT1 sOdd,
  .block (bitOf sB aT3),
  sel aT4 aZero aNM sB,
  sub3 (B + 2) aT3 aT4,
  .block [.load .w .r0 .r31 sB, .logic .xor .r9 .r9 .r0],
  half (B + 2)])

/-- `32 w` iterations of two steps, counted down in `r4`. -/
def inverse : Prog isa :=
  .seq (.block [.lsl .r4 .r29 5])
    (.loop (.seq (invStep 0 4) (.seq (invStep 4 0) (.block [.subi .r4 .r4 1]))) (.nonzero .d .r4))

end VG.Impl.Rsa.PPC64LE.Keys
