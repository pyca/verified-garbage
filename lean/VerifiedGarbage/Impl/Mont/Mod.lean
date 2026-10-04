/-!
# A modulus for Montgomery arithmetic, on any target

What the Montgomery arithmetic of each target (`Impl/Mont/<Target>.lean`)
needs of an odd multiword modulus `m`: its number of 64-bit words `n`, where
it is in the working space (`mo`, `n` words), the working space's temporary
area (`tmp`, `n` words), `minv = -m⁻¹ mod 2⁶⁴`, and how a reduction step
may add a multiple of `m` (`red`).

A reduction step adds `u m` to the accumulator `T` for the `u` that makes
its low word zero, and divides by `2⁶⁴`. When `m ≡ -1 (mod 2⁶⁴)` (P-256's
`p`), `u` is `T`'s low word `t₀`, and `(T + t₀ m) / 2⁶⁴ = ⌊T / 2⁶⁴⌋ + t₀ m'`
for `m' = (m + 1) / 2⁶⁴`, whose words may be zero or powers of two, which
need no multiplication (`Red.friendly`, with `m'`'s words as `MWord`s).
-/

namespace VG.Impl.Mont

/-- A word of a constant multiplicand, as the code multiplies by it: zero,
one, `2^k` (`0 < k < 64`), or any other value. -/
inductive MWord
  | zero
  | one
  | pow2 (k : Nat)
  | gen (v : Nat)
  deriving DecidableEq, Repr

namespace MWord

/-- The word's value. -/
def val : MWord → Nat
  | zero => 0
  | one => 1
  | pow2 k => 2 ^ k
  | gen v => v

/-- The word `w` (below `2⁶⁴`), classified. -/
def ofNat (w : Nat) : MWord :=
  if w = 0 then zero
  else if w = 1 then one
  else match (List.range 64).find? (fun k => 2 ^ k == w) with
    | some k => pow2 k
    | none => gen w

end MWord

/-- How a reduction step adds a multiple of the modulus: `general` (by
`u = t₀ minv`, and the modulus's words in the working space), or `friendly`
for `m ≡ -1 (mod 2⁶⁴)`, with the words of `m' = (m + 1) / 2⁶⁴`. -/
inductive Red
  | general
  | friendly (ws : List MWord)
  deriving DecidableEq, Repr

/-- The reduction of the `n`-word modulus `m`: `friendly` if
`m ≡ -1 (mod 2⁶⁴)`, else `general`. -/
def Red.ofModulus (n m : Nat) : Red :=
  if m % 2 ^ 64 = 2 ^ 64 - 1 then
    .friendly ((List.range n).map fun j => MWord.ofNat ((m + 1) / 2 ^ 64 / 2 ^ (64 * j) % 2 ^ 64))
  else .general

/-- A modulus: its number of words `n`, where it is (`mo`, `n` words), the
working space's temporary area (`tmp`, `n` words), `minv = -m⁻¹ mod 2⁶⁴`,
and its reduction (`red`, which only some targets use). -/
structure Mod where
  n : Nat
  mo : Nat
  tmp : Nat
  minv : BitVec 64
  red : Red := .general

end VG.Impl.Mont
