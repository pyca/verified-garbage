import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Packed divsteps on 64-bit words: the definitions

A chunk of divsteps on one word per row of the matrix (`pstep`), apart from
their proofs (`Packed.lean`), so that code proven to compute them needs no
algebra.

The rows are `u P + v Q` and `q P + r Q` modulo `2^64`, for `P` and `Q`
congruent to `f` and `g` modulo `2^n` (`n` the chunk's steps). They change
as `(f, g)` would, doubled rather than halved: after `j` steps their low
`n` bits are `2^j f_j` and `2^j g_j`'s, so step `j` reads `g`'s parity from
bit `j`. `E = ~d` holds `d`, its sign bit set for `d ≥ 0`.
-/

namespace VG.Proof.Divstep

/-- The packed divstep at bit `j` (`j ≤ 62`) on `E = ~d` and the rows `F`,
`G`: `G << (63 - j)` is `2^63` for an odd `g` and `0` for an even one, and
adding `E` to it carries for an odd `g` and `d ≥ 0` (the swap). -/
def pstep (j : Nat) (w : BitVec 64 × BitVec 64 × BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 :=
  if 2 ^ 64 ≤ (w.2.2 <<< (63 - j)).toNat + w.1.toNat then (-2 - w.1 - 2, w.2.2 + w.2.2, w.2.2 - w.2.1)
  else if w.2.2 <<< (63 - j) = 0 then (w.1 - 2, w.2.1 + w.2.1, w.2.2)
  else (w.1 - 2, w.2.1 + w.2.1, w.2.2 + w.2.1)

/-- Steps at bits `0 … n - 1`. -/
def psteps : Nat → BitVec 64 × BitVec 64 × BitVec 64 → BitVec 64 × BitVec 64 × BitVec 64
  | 0, w => w
  | n + 1, w => pstep n (psteps n w)

/-- What makes the fields of a row nonnegative: `2^30` below bit 31, `2^14`
at bits 31 and 47. -/
def pextC : BitVec 64 := 2 ^ 30 + 2 ^ 45 + 2 ^ 61

/-- The row's entry at bit 47 (`v` or `r`), once `pextC` is added. -/
def pextHi (x : BitVec 64) : BitVec 64 := ((x + pextC) >>> 47) - 16384

/-- The row's entry at bit 31 (`u` or `q`), once `pextC` is added. -/
def pextLo (x : BitVec 64) : BitVec 64 := (((x + pextC) <<< 17) >>> 48) - 16384

end VG.Proof.Divstep
