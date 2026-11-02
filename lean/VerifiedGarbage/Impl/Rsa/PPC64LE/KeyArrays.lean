module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.KeyWs

/-!
# More arrays of the key working space on PPC64LE

After the arrays 0–7 of `KeyWs.lean`: `m`, the negated modulus
`2^(32 w) - m`, zero, and four temporaries, which `vg_rsa_crt_values` and
key generation use.
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

end VG.Impl.Rsa.PPC64LE.Keys
