import VerifiedGarbage.Spec.Ed448.Point56
import VerifiedGarbage.Spec.X448.Field64

/-!
# Ed448's point doubling and addition in radix `2^64`, as functions

**Trusted** (as every file in `Spec/`). The contracts of functions on points
of edwards448 in projective coordinates (`Point`), each coordinate an
element of `Spec/X448/Field64.lean` (seven 64-bit words, the x86-64 code's
representation), so that Ed448's x86-64 code (base-point multiplication and
verification) can call one copy of each instead of repeating it at every
use:

* `vg_ed448_r64_point_double`: `p` doubled, by RFC 8032 §5.2.4's doubling
  formulas (`Point56.pointDouble`);
* `vg_ed448_r64_point_add_affine`: the sum `p + q`, by the specification's
  complete addition formula (`pointAdd`), for `q` with `Z = 1`: `q` is given
  by its `X` and `Y` alone.

They are not algorithms of a standard but the arithmetic Ed448 is built
from, in the representation that code keeps points in: what they compute is
stated on the coordinates as elements of `GF(p)`, `p = 2^448 - 2^224 - 1`.

A coordinate is 56 bytes, a little-endian number below `2^448` standing for
its residue modulo `p` (`elemAt`): any 56 bytes are a coordinate. The
coordinates live in Ed448's working space `ws` of 8192 bytes (`[u64; 1024]`)
in slots of 64 bytes, slot `n` at byte `64 + 64 n` (`Field64.slotAt`), of
which a coordinate takes the first 56 bytes; a point is three coordinates,
`X, Y, Z`, in consecutive slots (`pointAt`), at the slots where that code
keeps them. The doubling replaces `p`, in slots 0 to 2. The addition reads
`p` in slots 0 to 2, `q`'s `X` and `Y` in slots 8 and 9, and `d` in slot 11,
and writes the sum to slots 3 to 5. Bytes 832 to 1647 of `ws` (slots 12 to
21 and the 176 bytes above them, as `Field64`'s `vg_gf448_r64_pow223` uses
them) are the functions' own working space. On return they are unspecified
and may hold intermediate values; every other byte of `ws` keeps its value
but the result's (`Keeps`).

Everything is secret but the pointer, which is public, and the functions are
constant time.
-/

namespace VG.Spec.Ed448.Point64

open X448 (Fe P)
open X448.Field64 (wsBytes slotAt valAt)

/-- The coordinate at byte offset `o` of the working space `ws`: its 56
bytes, little-endian, modulo `P`. -/
def elemAt (m : Mem) (ws : Addr) (o : Nat) : Fe := Fin.ofNat P (valAt m ws o)

/-- The point in slots `n`, `n + 1` and `n + 2`. -/
def pointAt (m : Mem) (ws : Addr) (n : Nat) : Point :=
  ⟨elemAt m ws (slotAt n), elemAt m ws (slotAt (n + 1)), elemAt m ws (slotAt (n + 2))⟩

/-- Where `p` is, and the double: slots 0 to 2. -/
def pSlot : Nat := 0

/-- Where the sum is: slots 3 to 5. -/
def sumSlot : Nat := 3

/-- Where `q`'s `X` and `Y` are: slots 8 and 9. -/
def qSlot : Nat := 8

/-- Where the addition needs `d`: slot 11. -/
def dSlot : Nat := 11

/-- The point with coordinates `(x : y : 1)`. -/
def affine (x y : Fe) : Point := ⟨x, y, 1⟩

/-- Where the functions' own working space starts: slot 12. -/
def ownAt : Nat := slotAt 12

/-- Where it ends. -/
def ownEnd : Nat := 1648

/-- Every byte of `ws` but those of the result (the three slots from slot
`r`) and of the functions' own working space (bytes 832 to 1647) keeps its
value. -/
def Keeps (r : Nat) (ws : Addr) (m m' : Mem) : Prop :=
  ∀ i < wsBytes, (i < slotAt r ∨ slotAt (r + 3) ≤ i) → (i < ownAt ∨ ownEnd ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

/-- `ws: *mut [u64; 1024]`, the pointer public. -/
def sig : Sig where
  params := [("ws", .array true .u64 1024)]

/-- `Point56.pointDouble`: the point in slots 0 to 2 is doubled. -/
def doubleContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (post := fun ws m m' _ =>
      pointAt m' ws pSlot = Point56.pointDouble (pointAt m ws pSlot) ∧ Keeps pSlot ws m m')
    (stack := stack)

/-- `pointAdd`: with `d` in slot 11, slots 3 to 5 become the sum of the point
in slots 0 to 2 and the point `(x : y : 1)` for `x` and `y` in slots 8 and 9. -/
def addAffineContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws m => elemAt m ws (slotAt dSlot) = d)
    (post := fun ws m m' _ =>
      pointAt m' ws sumSlot = pointAdd (pointAt m ws pSlot)
          (affine (elemAt m ws (slotAt qSlot)) (elemAt m ws (slotAt (qSlot + 1)))) ∧
        Keeps sumSlot ws m m')
    (stack := stack)

/-- The Rust module of the functions. -/
def module : String := "ed448_r64"

/-- What both functions' documentation says of their elements. -/
def elemDoc : String :=
  "A point is three coordinates `X, Y, Z` in consecutive slots; slot `n` of `ws` is the 64 \
    bytes from byte `64 + 64 n`, of which a coordinate takes the first 56: a little-endian \
    number below `2^448`, standing for its residue modulo `p = 2^448 - 2^224 - 1`, not \
    necessarily reduced. Every byte of `ws` but the result's and the function's own working \
    space (bytes 832 to 1647) keeps its value."

/-- What both functions require. -/
def safety : List String :=
  ["Bytes 832 to 1647 of `ws` are unspecified on return and may hold intermediate values, \
      which the caller must destroy if they are secret."]

/-- `vg_ed448_r64_point_double` on every target. -/
def doubleApi : Api where
  module := module
  name := "vg_ed448_r64_point_double"
  sig := sig
  contracts := some fun A stack => doubleContract A stack
  summary := "Point doubling on edwards448: replaces the point in slots 0 to 2 of the working \
    space `ws` (bytes 64 to 255) with its double, by RFC 8032's doubling formulas in \
    projective coordinates (§5.2.4). " ++ elemDoc ++ "\n\n\
    Contract: `doubleContract` of `VG.Spec.Ed448.Point64`. Constant time: only the pointer may \
    affect timing."
  safety := safety

/-- `vg_ed448_r64_point_add_affine` on every target. -/
def addAffineApi : Api where
  module := module
  name := "vg_ed448_r64_point_add_affine"
  sig := sig
  contracts := some fun A stack => addAffineContract A stack
  summary := "Point addition on edwards448: writes to slots 3 to 5 of the working space `ws` \
    (bytes 256 to 447) the sum of the point in slots 0 to 2 (bytes 64 to 255) and the point \
    `(x : y : 1)`, for `x` and `y` in slots 8 and 9 (bytes 576 and 640), by RFC 8032's \
    complete addition formula in projective coordinates (§5.2.4), with `d` read from slot 11 \
    (byte 768). " ++ elemDoc ++ "\n\n\
    Contract: `addAffineContract` of `VG.Spec.Ed448.Point64`. Constant time: only the pointer \
    may affect timing."
  safety := ("Slot 11 of `ws` (byte 768) must hold an element congruent to edwards448's `d`, \
    `-39081`, modulo `p`." :: safety)

end VG.Spec.Ed448.Point64
