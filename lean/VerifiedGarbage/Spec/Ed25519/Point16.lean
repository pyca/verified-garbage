module

public import VerifiedGarbage.Spec.Ed25519
public import VerifiedGarbage.Spec.X25519.Field16

/-!
# Ed25519's point addition and doubling in radix `2^16`, as functions

**Trusted** (as every file in `Spec/`). The contracts of functions on points
of edwards25519 in extended coordinates (`Point`), each coordinate sixteen
16-bit limbs, so that the Ed25519 code that keeps points this way (the ARMv7
code) can call one copy of each instead of repeating it at every use:

* `vg_ed25519_r16_point_add`: the sum `p + q`, by the specification's
  complete addition formula (`pointAdd`);
* `vg_ed25519_r16_point_double`: the sum `p + p`, by the same formula.

They are not algorithms of a standard but the arithmetic Ed25519 is built
from, in the representation that code keeps points in: what they compute is
stated on the coordinates as elements of `GF(p)`, `p = 2^255 - 19`.

A coordinate is an element of `Spec/X25519/Field16.lean`: sixteen limbs,
each a 32-bit little-endian word below `2^16`, least significant first
(`Field16.Limbs`), standing for the residue of `Σ lᵢ 2^(16 i)` modulo `p`
(`elemAt`). A point is four coordinates, `X, Y, Z, T`, at consecutive
offsets (`pointAt`, `PointLimbs`). The points live in Ed25519's working
space `ws` of 8192 bytes (`[u64; 1024]`), at fixed offsets, where that code
keeps the operands of its additions: `p` at byte 64 (`pAt`), `q` at byte 320
(`qAt`), and the curve's constant `d` at byte 1088 (`dAt`), which the caller
provides; the result replaces `p`. Bytes 576 to 1087 (`tmpAt` to `dAt`) and
1472 to 1631 (`Field16.ownAt` to `Field16.ownEnd`, the product's limbs and
room to save the registers the functions use, so that they need no stack) of
`ws` are the functions' own working space. On return they are unspecified
and may hold intermediate values; every other byte of `ws` keeps its value
but the result's (`Keeps`).

The result's limbs are below `2^16` again, so that it can be an operand.
Everything is secret but the pointer, which is public, and the functions are
constant time.
-/

@[expose] public section

namespace VG.Spec.Ed25519.Point16

open X25519 (P Fe)
open X25519.Field16 (Limbs valAt ownAt ownEnd)

/-- The bytes of the working space. -/
def wsBytes : Nat := 8192

/-- The bytes of a coordinate: a 32-bit word per limb. -/
def elemBytes : Nat := X25519.Field16.elemBytes

/-- Where the first point, and the result, is. -/
def pAt : Nat := 64

/-- Where the second point is. -/
def qAt : Nat := 320

/-- Where the functions' own elements start; they end at `dAt`. -/
def tmpAt : Nat := 576

/-- Where `d` is. -/
def dAt : Nat := 1088

/-- The coordinate at byte offset `o` of the working space `ws`: its limbs'
value modulo `P`. -/
def elemAt (m : Mem) (ws : Addr) (o : Nat) : Fe :=
  Fin.ofNat P (valAt m ws (BitVec.ofNat 32 o))

/-- The point at byte offset `o`: its coordinates `X, Y, Z, T` at `o`,
`o + 64`, `o + 128` and `o + 192`. -/
def pointAt (m : Mem) (ws : Addr) (o : Nat) : Point :=
  ⟨elemAt m ws o, elemAt m ws (o + elemBytes), elemAt m ws (o + 2 * elemBytes),
    elemAt m ws (o + 3 * elemBytes)⟩

/-- Every limb of each coordinate of the point at `o` is below `2^16`. -/
def PointLimbs (m : Mem) (ws : Addr) (o : Nat) : Prop :=
  ∀ j < 4, Limbs m ws (BitVec.ofNat 32 (o + elemBytes * j))

/-- Every byte of `ws` but those of the result (bytes 64 to 319) and of the
functions' own working space (bytes 576 to 1087 and 1472 to 1631) keeps its
value. -/
def Keeps (ws : Addr) (m m' : Mem) : Prop :=
  ∀ i < wsBytes, (i < pAt ∨ qAt ≤ i) → (i < tmpAt ∨ dAt ≤ i) → (i < ownAt ∨ ownEnd ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

/-- `ws: *mut [u64; 1024]`, the pointer public. -/
def sig : Sig where
  params := [("ws", .array true .u64 1024)]

/-- `pointAdd`: with `d` at `dAt` and every operand's limbs below `2^16`, the
point at `pAt` becomes the sum of the points at `pAt` and `qAt`, with limbs
below `2^16`. -/
def addContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws m => PointLimbs m ws pAt ∧ PointLimbs m ws qAt ∧
      Limbs m ws (BitVec.ofNat 32 dAt) ∧ elemAt m ws dAt = d)
    (post := fun ws m m' _ =>
      PointLimbs m' ws pAt ∧
        pointAt m' ws pAt = pointAdd (pointAt m ws pAt) (pointAt m ws qAt) ∧ Keeps ws m m')
    (stack := stack)

/-- `pointAdd` of a point and itself: with `d` at `dAt` and every operand's
limbs below `2^16`, the point at `pAt` is doubled, with limbs below `2^16`. -/
def doubleContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws m => PointLimbs m ws pAt ∧ Limbs m ws (BitVec.ofNat 32 dAt) ∧
      elemAt m ws dAt = d)
    (post := fun ws m m' _ =>
      PointLimbs m' ws pAt ∧
        pointAt m' ws pAt = pointAdd (pointAt m ws pAt) (pointAt m ws pAt) ∧ Keeps ws m m')
    (stack := stack)

/-- What both functions' documentation says of their elements. -/
def elemDoc : String :=
  "A point is four coordinates `X, Y, Z, T` of 64 bytes each, consecutive; a coordinate is \
    sixteen 32-bit little-endian words, least significant first, each a limb below `2^16`, \
    standing for the residue of `Σ l_i 2^(16 i)` modulo `p = 2^255 - 19`. The 64 bytes at byte \
    1088 must hold the curve's constant `d`. The result's limbs are below `2^16`. Every byte \
    of `ws` but the result's and the function's own working space (bytes 576 to 1087 and 1472 \
    to 1631) keeps its value."

/-- What both functions require. -/
def safetyDoc (points : String) : List String :=
  [s!"Each limb of {points} and of the 64 bytes at byte 1088 of `ws` must be below `2^16`, \
      and the latter must be congruent to the curve's constant `d` modulo `p`.",
    "Bytes 576 to 1087 and 1472 to 1631 of `ws` are unspecified on return and may hold \
      intermediate values, which the caller must destroy if they are secret."]

/-- `vg_ed25519_r16_point_add` on every target. -/
def addApi : Api where
  module := "ed25519_r16"
  name := "vg_ed25519_r16_point_add"
  sig := sig
  contracts := some fun A stack => addContract A stack
  summary := "Point addition on edwards25519: replaces the point at byte 64 of the working \
    space `ws` with its sum with the point at byte 320, by RFC 8032's complete addition \
    formula in extended coordinates. " ++ elemDoc ++ "\n\n\
    Contract: `addContract` of `VG.Spec.Ed25519.Point16`. Constant time: only the pointer may \
    affect timing."
  safety := safetyDoc "the points at bytes 64 and 320 of `ws`"

/-- `vg_ed25519_r16_point_double` on every target. -/
def doubleApi : Api where
  module := "ed25519_r16"
  name := "vg_ed25519_r16_point_double"
  sig := sig
  contracts := some fun A stack => doubleContract A stack
  summary := "Point doubling on edwards25519: replaces the point at byte 64 of the working \
    space `ws` with its sum with itself, by RFC 8032's complete addition formula in extended \
    coordinates. " ++ elemDoc ++ "\n\n\
    Contract: `doubleContract` of `VG.Spec.Ed25519.Point16`. Constant time: only the pointer \
    may affect timing."
  safety := safetyDoc "the point at byte 64 of `ws`"

end VG.Spec.Ed25519.Point16
