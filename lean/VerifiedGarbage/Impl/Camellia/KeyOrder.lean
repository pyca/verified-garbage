import VerifiedGarbage.Spec.Camellia

/-!
# The order of Camellia's subkeys

The subkeys as `vg_camellia_expand_key` stores them, in the order of
`Spec.Camellia.scheduleWords`: each the high or low half of one of `KL`,
`KR`, `KA` and `KB` (`0 … 3`) rotated left by some bits (RFC 3713 §2.2).
Every target's key schedule computes and stores them in this order. And
the planes of the constants `Sigma1 … Sigma6`, which every target's key
schedule stores as a table of subkeys for its bitsliced rounds.
-/

namespace VG.Impl.Camellia

def KL : Nat := 0
def KR : Nat := 1
def KA : Nat := 2
def KB : Nat := 3

/-- The subkeys of a key of 16 bytes (RFC 3713 §2.2), in the stored order:
value, rotation and half of each. -/
def subkeys128 : List (Nat × Nat × Bool) :=
  [(KL, 0, true), (KL, 0, false),
   (KA, 0, true), (KA, 0, false), (KL, 15, true), (KL, 15, false), (KA, 15, true), (KA, 15, false),
   (KA, 30, true), (KA, 30, false),
   (KL, 45, true), (KL, 45, false), (KA, 45, true), (KL, 60, false), (KA, 60, true), (KA, 60, false),
   (KL, 77, true), (KL, 77, false),
   (KL, 94, true), (KL, 94, false), (KA, 94, true), (KA, 94, false), (KL, 111, true), (KL, 111, false),
   (KA, 111, true), (KA, 111, false)]

/-- The subkeys of a key of 24 or 32 bytes, in the stored order. -/
def subkeys256 : List (Nat × Nat × Bool) :=
  [(KL, 0, true), (KL, 0, false),
   (KB, 0, true), (KB, 0, false), (KR, 15, true), (KR, 15, false), (KA, 15, true), (KA, 15, false),
   (KR, 30, true), (KR, 30, false),
   (KB, 30, true), (KB, 30, false), (KL, 45, true), (KL, 45, false), (KA, 45, true), (KA, 45, false),
   (KL, 60, true), (KL, 60, false),
   (KR, 60, true), (KR, 60, false), (KB, 60, true), (KB, 60, false), (KL, 77, true), (KL, 77, false),
   (KA, 77, true), (KA, 77, false),
   (KR, 94, true), (KR, 94, false), (KA, 94, true), (KA, 94, false), (KL, 111, true), (KL, 111, false),
   (KB, 111, true), (KB, 111, false)]

/-- The byte of a half that position `c` of a plane holds (as `toBs` lays out a half). -/
def bytePos (c : Nat) : Nat := c / 2 + 4 * (c % 2)

/-- Plane `j` of the subkey `x` in every lane, as the table holds it: bit
`8 c + b` is bit `j` of byte `bytePos c` of `x`, the most significant first. -/
def keyPlane (x : BitVec 64) (j : Nat) : BitVec 64 :=
  (BitVec.ofBoolListLE ((List.range 64).map fun p => x.getLsbD (56 - 8 * bytePos (p / 8) + j))).setWidth 64

/-- The subkeys of the pairs. -/
def sigmas : List (BitVec 64) :=
  [Spec.Camellia.sigma1, Spec.Camellia.sigma2, Spec.Camellia.sigma3, Spec.Camellia.sigma4,
    Spec.Camellia.sigma5, Spec.Camellia.sigma6]

end VG.Impl.Camellia
