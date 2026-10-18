module

public import VerifiedGarbage.Impl.Rsa.X86.KeyWs

/-! # The inverse modulo an odd number, on i686

`inverse`: `32 w` iterations of two steps of the binary extended Euclidean
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

/-- `[o] := [a] - [b] mod m` for `[a], [b] < m`, through `aT1` and `aT4`. -/
def subModP (n o a b : Nat) : List (Prog isa) :=
  [sub3 n aT1 a b, .block [.store (sc sB) .ebx], sel n aT4 aZero aNM sB, sub3 n o aT1 aT4]

/-- One step from the bank at `A` to the bank at `B`. -/
def invStep (n A B : Nat) : Prog isa := seqs ([
  .block (bitOf n sOdd A),
  sub3 n aT1 A (A + 1),
  .block ([.store (sc sB) .ebx] ++ andS sC sOdd sB),
  sub3 n aT2 (A + 1) A,
  sel n (B + 1) (A + 1) A sC,
  sel n aT3 aT1 aT2 sC,
  sel n B A aT3 sOdd,
  .block [.mov .ebx (.imm 0)],
  half n B] ++
  subModP n aT3 (A + 2) (A + 3) ++ subModP n aT2 (A + 3) (A + 2) ++ [
  sel n (B + 3) (A + 3) (A + 2) sC,
  sel n aT1 aT3 aT2 sC,
  sel n aT3 (A + 2) aT1 sOdd,
  .block (bitOf n sB aT3),
  sel n aT4 aZero aNM sB,
  sub3 n (B + 2) aT3 aT4,
  .block [.alu .xor .ebx (.mem (sc sB))],
  half n (B + 2)])

/-- `32 w` iterations of two steps, counted down in `esi`. -/
def inverse (n : Nat) : Prog isa :=
  .seq (.block [.mov .esi (.imm (BitVec.ofNat 32 (32 * n)))])
    (.loop (.seq (invStep n 0 4) (.seq (invStep n 4 0) (.block [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)]))) .ne)

end VG.Impl.Rsa.X86.Keys
