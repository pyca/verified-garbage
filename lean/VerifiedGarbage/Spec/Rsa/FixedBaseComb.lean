module

public import VerifiedGarbage.Spec.Rsa.Contract

/-!
# Public fixed-base Montgomery comb precomputation

**Trusted.** A five-tooth comb for repeated exponentiation with one public
modulus and base. The representation uses RSA's existing public Montgomery
precomputation and canonical little-endian 64-bit words. It contains no
pointers and does not depend on an arithmetic backend.

The table follows the fixed-base comb idea of Lim and Lee, "More Flexible
Exponentiation with Precomputation", CRYPTO 1994. Its precise meaning here
is the exponent-column formula below: for `d = rows bits`, bit `i + j*d`
contributes `2^i * 2^(j*d)` to the exponent. No new sampling or group policy
is introduced by this arithmetic representation.
-/

@[expose] public section
namespace VG.Spec.Rsa.FixedBaseComb

/-- Five exponent columns. -/
def teeth : Nat := 5

def entries : Nat := 2 ^ teeth

/-- The public number of rows, with zero padding above the maximum width. -/
def rows (bits : Nat) : Nat := (bits + teeth - 1) / teeth

/-- Entry `digit` combines the columns at offsets `j * rows bits`.
For an exponent `x`, row `i` selects the entry whose bit `j` is bit
`i + j * rows bits` of `x`. Processing the rows from high to low with
one square and one product per row yields `g^x`. -/
def exponent (bits digit : Nat) : Nat :=
  ((List.range teeth).map fun j => (digit / 2 ^ j % 2) * 2 ^ (j * rows bits)).foldl (· + ·) 0

/-- Thirty-two reduced Montgomery residues, each exactly `w` words.
Entry zero is Montgomery one, so a zero digit still performs a product. -/
def table (p g bits w : Nat) : List (BitVec 64) :=
  (List.range entries).flatMap fun digit =>
    toWords (powMod g (exponent bits digit) p * 2 ^ (64 * w) % p) w

/-- RSA's modulus/R-squared prefix followed by the fixed-base comb table. -/
def precompute (modulus : List Byte) (g bits : Nat) : Option (List (BitVec 64)) := do
  let montgomery ← publicPrecompute modulus
  return montgomery ++ table (os2ip modulus) g bits (modulusWords modulus.length)

/-- Two RSA Montgomery residues and thirty-two comb entries. -/
def precomputedWords (modulusLength : Nat) : Nat :=
  Rsa.precomputedWords modulusLength + entries * modulusWords modulusLength

end VG.Spec.Rsa.FixedBaseComb
