import VerifiedGarbage.Spec.Ed25519
import VerifiedGarbage.TCB.Artifact

/-!
# Ed25519's point addition in radix `2^32`, as a function

**Trusted** (as every file in `Spec/`). The contract of a function on points
of edwards25519 in extended coordinates (`Point`), each coordinate eight
32-bit words, so that the Ed25519 code that keeps points this way (the x86
code) can call one copy of the addition instead of repeating it at every
use:

* `vg_ed25519_r32_point_add`: the sum `p + q`, by the specification's
  complete addition formula (`pointAdd`).

It is not an algorithm of a standard but the arithmetic Ed25519 is built
from, in the representation that code keeps points in: what it computes is
stated on the coordinates as elements of `GF(p)`, `p = 2^255 - 19`.

A coordinate is 32 bytes, a little-endian number below `2^256`, standing for
its residue modulo `p` (`elemAt`): any 32 bytes are a coordinate. A point is
four coordinates, `X, Y, Z, T`, at consecutive offsets (`pointAt`). The
points live in Ed25519's working space `ws` of 8192 bytes (`[u64; 1024]`),
at fixed offsets, where that code keeps the operands of its additions: `p` at
byte 64 (`pAt`), `q` at byte 192 (`qAt`), and the curve's constant `d` at
byte 576 (`dAt`), which the caller provides; the sum replaces `p`. Bytes 320
to 575 and 864 to 1023 of `ws` are the function's own working space. On
return they are unspecified and may hold intermediate values; every other
byte of `ws` keeps its value but the sum's (`Keeps`).

Everything is secret but the pointer, which is public, and the function is
constant time.
-/

namespace VG.Spec.Ed25519.Point32

open X25519 (P Fe)

/-- The bytes of the working space. -/
def wsBytes : Nat := 8192

/-- The bytes of a coordinate. -/
def elemBytes : Nat := 32

/-- Where the first point, and the sum, is. -/
def pAt : Nat := 64

/-- Where the second point is. -/
def qAt : Nat := 192

/-- Where `d` is. -/
def dAt : Nat := 576

/-- The coordinate at byte offset `o` of the working space `ws`: its 32
bytes, little-endian, modulo `P`. -/
def elemAt (m : Mem) (ws : Addr) (o : Nat) : Fe :=
  Fin.ofNat P (m.read (ws + BitVec.ofNat 64 o) elemBytes).toNat

/-- The point at byte offset `o`: its coordinates `X, Y, Z, T` at `o`,
`o + 32`, `o + 64` and `o + 96`. -/
def pointAt (m : Mem) (ws : Addr) (o : Nat) : Point :=
  ⟨elemAt m ws o, elemAt m ws (o + elemBytes), elemAt m ws (o + 2 * elemBytes),
    elemAt m ws (o + 3 * elemBytes)⟩

/-- Every byte of `ws` but those of the sum (bytes 64 to 191) and of the
function's own working space (bytes 320 to 575 and 864 to 1023) keeps its
value. -/
def Keeps (ws : Addr) (m m' : Mem) : Prop :=
  ∀ i < wsBytes, (i < pAt ∨ pAt + 4 * elemBytes ≤ i) → (i < 320 ∨ 576 ≤ i) → (i < 864 ∨ 1024 ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

/-- `ws: *mut [u64; 1024]`, the pointer public. -/
def sig : Sig where
  params := [("ws", .array true .u64 1024)]

/-- `pointAdd`: with `d` at `dAt`, the point at `pAt` becomes the sum of the
points at `pAt` and `qAt`. -/
def addContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws m => elemAt m ws dAt = d)
    (post := fun ws m m' _ =>
      pointAt m' ws pAt = pointAdd (pointAt m ws pAt) (pointAt m ws qAt) ∧ Keeps ws m m')
    (stack := stack)

/-- `vg_ed25519_r32_point_add` on every target. -/
def addApi : Api where
  module := "ed25519_r32"
  name := "vg_ed25519_r32_point_add"
  sig := sig
  contracts := some fun A stack => addContract A stack
  summary := "Point addition on edwards25519: replaces the point at byte 64 of the working \
    space `ws` with its sum with the point at byte 192, by RFC 8032's complete addition \
    formula in extended coordinates. A point is four coordinates `X, Y, Z, T` of 32 bytes \
    each, consecutive; a coordinate is a little-endian number below `2^256` standing for its \
    residue modulo `p = 2^255 - 19`. The 32 bytes at byte 576 must hold the curve's constant \
    `d`. Every byte of `ws` but the sum's and the function's own working space (bytes 320 to \
    575 and 864 to 1023) keeps its value.\n\n\
    Contract: `addContract` of `VG.Spec.Ed25519.Point32`. Constant time: only the pointer may \
    affect timing."
  safety :=
    ["The 32 bytes at byte 576 of `ws` must be congruent to the curve's constant `d` modulo \
        `p`.",
      "Bytes 320 to 575 and 864 to 1023 of `ws` are unspecified on return and may hold \
        intermediate values, which the caller must destroy if they are secret."]

end VG.Spec.Ed25519.Point32
