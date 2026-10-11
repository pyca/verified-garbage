/-!
# Planes of Camellia's 64-bit constants, on 32-bit targets

The tables of bitsliced subkeys on the 32-bit targets hold sixteen 32-bit
planes for each subkey: plane `j` of its left 32 bits (`w = 0`) or right
(`w = 1`), bit `8 i + b` being bit `j` of byte `4 w + i` of the subkey (the
most significant first) in every lane `b`. The key schedules store the
constants `Sigma1 … Sigma6` this way, as immediates.
-/

namespace VG.Impl.Camellia

/-- The bits `p < n` of plane `j` of word `w` (0 for the left 32 bits, 1 for
the right) of `x` in every lane, as a number. -/
def planeBits32 (x : BitVec 64) (w j : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => planeBits32 x w j n |||
      (if x.getLsbD (56 - 8 * (4 * w + n / 8) + j) then 2 ^ n else 0)

/-- Plane `j` of word `w` of the subkey `x`, as the table holds it: bit
`8 i + b` is bit `j` of byte `4 w + i` of `x`, the most significant first. -/
def keyPlane32 (x : BitVec 64) (w j : Nat) : BitVec 32 := BitVec.ofNat 32 (planeBits32 x w j 32)

end VG.Impl.Camellia
