import VerifiedGarbage.Spec.Ed448.Point56

/-!
# Ed448's fixed-base comb in radix `2^56`, as a function

**Trusted** (as every file in `Spec/`). The contract of the comb that
multiplies edwards448's base point by a scalar in the AArch64 code of X448
and Ed448, so that X448's multiplication of the base point, Ed448's (public
keys and signatures) and Ed448's verification can call one copy of it
instead of repeating it:

* `vg_ed448_r56_comb_base`: for the scalar `k` of `8 n` bits, `n` 56 or 57,
  and its nibbles `n_i` (`nibble`), the two sums of the comb,
  `A = [Σ_{j < n} n_{2j+1} 256^j] B` (`oddNibbles`) and
  `C = [Σ_{j < n} n_{2j} 256^j] B` (`evenNibbles`), in projective
  coordinates, from which the caller computes `[k] B = [16] A + C`.

It is not an algorithm of a standard but a step of the ones that use it:
every caller uses only the point `[k] B`, not its coordinates (it encodes
it, takes `y² / x²` of it, or compares it with another point), so the
contract states the two points, not their coordinates: each is equal to
`pointMul` of its sum and `basePoint` (`pointEqual`, which compares the
affine coordinates without an inversion), with `Z` nonzero.

The scalar is given as its bits, a byte each, least significant first,
from byte 3072 of the working space (`bitsAt`): the code reads them as the
comb's digits. A point is three coordinates `X, Y, Z` in consecutive slots of
the working space, each an element of `Spec/X448/Field56.lean` (eight limbs
of 56 bits): `A` in slots 0 to 2 and `C` in slots 3 to 5. The function needs
and keeps `Field56.Bounded` (every limb of every slot below `3·2^56 + 2^9`) and slot
19 zero, every limb 0. It writes the 22 slots (bytes 64 to 2879) and its
own bytes (`Field56.own`); on return those, but the results, are
unspecified and may hold intermediate values, and every other byte of `ws`
keeps its value (`Field56.Keeps`).

Everything is secret but the pointer and `n`, which are public, and the
function is constant time.
-/

namespace VG.Spec.Ed448.Comb56

open X448.Field56 (slotAt limbAt limbs elemAt Bounded Keeps own)
open Point56 (pointAt zeroSlot)

/-- Where the scalar's bits are, a byte each. -/
def bitsOff : Nat := 3072

/-- The scalar whose `t` bits are the bytes from `bitsOff`, least significant first. -/
def bitsAt (m : Mem) (ws : Addr) : Nat → Nat
  | 0 => 0
  | t + 1 => bitsAt m ws t + 2 ^ t * (m (ws + BitVec.ofNat 64 (bitsOff + t))).toNat

/-- Each of the first `t` bytes from `bitsOff` is a bit. -/
def IsBits (m : Mem) (ws : Addr) (t : Nat) : Prop :=
  ∀ i < t, (m (ws + BitVec.ofNat 64 (bitsOff + i))).toNat < 2

/-- Nibble `i` of `k`. -/
def nibble (k i : Nat) : Nat := k / 16 ^ i % 16

/-- `Σ_{j < c} n_{2j+1} 256^j`, for the nibbles `n_i` of `k`. -/
def oddNibbles (k : Nat) : Nat → Nat
  | 0 => 0
  | c + 1 => oddNibbles k c + nibble k (2 * c + 1) * 256 ^ c

/-- `Σ_{j < c} n_{2j} 256^j`, for the nibbles `n_i` of `k`. -/
def evenNibbles (k : Nat) : Nat → Nat
  | 0 => 0
  | c + 1 => evenNibbles k c + nibble k (2 * c) * 256 ^ c

/-- What the function changes: the slots, and its own bytes. -/
def written : List (Nat × Nat) := (slotAt 0, slotAt X448.Field56.slots) :: own

/-- `ws: *mut [u64; 1024]` and `n: usize`, both public. -/
def sig : Sig where
  params := [("ws", .array true .u64 1024), ("n", .int .usize true)]

/-- The comb's sums: for `n` 56 or 57, with `8 n` bits of `k` from byte `bitsOff`, every slot
`Bounded` and every limb of slot 19 zero, the point in slots 0 to 2 equals
`pointMul (oddNibbles k n) basePoint` and the point in slots 3 to 5 equals
`pointMul (evenNibbles k n) basePoint`, each with `Z` nonzero. -/
def combBaseContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws n m => (n.toNat = 56 ∨ n.toNat = 57) ∧ IsBits m ws (8 * n.toNat) ∧
      Bounded m ws ∧ ∀ i < limbs, limbAt m ws (slotAt zeroSlot) i = 0)
    (post := fun ws n m m' _ =>
      Bounded m' ws ∧ elemAt m' ws (slotAt 2) ≠ 0 ∧ elemAt m' ws (slotAt 5) ≠ 0 ∧
        pointEqual (pointAt m' ws 0)
          (pointMul (oddNibbles (bitsAt m ws (8 * n.toNat)) n.toNat) basePoint) = true ∧
        pointEqual (pointAt m' ws 3)
          (pointMul (evenNibbles (bitsAt m ws (8 * n.toNat)) n.toNat) basePoint) = true ∧
        Keeps ws written m m')
    (stack := stack)

/-- `vg_ed448_r56_comb_base` on every target. -/
def combBaseApi : Api where
  module := "ed448_r56"
  name := "vg_ed448_r56_comb_base"
  sig := sig
  contracts := some fun A stack => combBaseContract A stack
  summary := "The fixed-base comb on edwards448: for the scalar `k` whose `8 n` bits, for `n` 56 or \
    57, are the bytes from byte 3072 of the working space `ws`, a bit (0 or 1) each, least \
    significant first, and its nibbles `n_i`, writes `A = [Σ_{j < n} n_{2j+1} 256^j] B` to slots 0 \
    to 2 of `ws` (bytes 64 to 447) and `C = [Σ_{j < n} n_{2j} 256^j] B` to slots 3 to 5 (bytes \
    448 to 831), for edwards448's base point `B` (RFC 8032 §5.2), in projective coordinates \
    `X, Y, Z` with `Z` nonzero, so that `[k] B = [16] A + C`. The coordinates are those of some \
    representation of each point: only the points are specified. Slot `n` of `ws` is the first \
    64 bytes from byte `64 + 128 n`, eight 64-bit little-endian words, least significant first, \
    each a limb: the number `Σ l_i 2^(56 i)`, standing for its residue modulo \
    `p = 2^448 - 2^224 - 1`, not necessarily reduced. Every byte of `ws` but the 22 slots (bytes 64 to 2879) and the function's own \
    working space (bytes 3584 to 4735) keeps its value.\n\n\
    Contract: `combBaseContract` of `VG.Spec.Ed448.Comb56`. Constant time: only the pointer and \
    `n` may affect timing."
  safety := [X448.Field56.boundedDoc,
    "`n` must be 56 or 57, and each of bytes 3072 to `3072 + 8 n - 1` of `ws` must be 0 or 1.",
    "Every limb of slot 19 of `ws` (bytes 2496 to 2559) must be 0.",
    "Bytes 64 to 2879 and 3584 to 4735 of `ws` but the results are unspecified on return and may \
      hold intermediate values, which the caller must destroy if they are secret."]

end VG.Spec.Ed448.Comb56
