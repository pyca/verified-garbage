module

public import VerifiedGarbage.Impl.Aes.AArch64.Linear

/-!
# Bitsliced AES on AArch64: the multiplication by `{04}`

InvMixColumns is MixColumns after multiplying each column by
`{04}x² + {05}`: `a'ᵣ = aᵣ ⊕ {04} • (aᵣ ⊕ aᵣ₊₂)`, since
`{0b}x³ + {0d}x² + {09}x + {0e} = ({03}x³ + {01}x² + {01}x + {02}) ({04}x² + {05})`
modulo `x⁴ + 1`. `times4` is the multiplication by `{04}` on the words of
the bitsliced state, as BearSSL's `aes_ct64` (Thomas Pornin, MIT licence)
computes it.
-/

@[expose] public section

namespace VG.Impl.Aes.AArch64

open VG.AArch64

/-- The words of `{04} • u` (bit `j` of each byte), from those of `u`:
the multiplication by `x²`, reduced by `{1b}`. -/
def times4 (j : Nat) : List Nat :=
  match j with
  | 0 => [6] | 1 => [6, 7] | 2 => [0, 7] | 3 => [1, 6]
  | 4 => [2, 6, 7] | 5 => [3, 7] | 6 => [4] | _ => [5]

end VG.Impl.Aes.AArch64
