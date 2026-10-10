import VerifiedGarbage.Spec.Weierstrass.Point
import VerifiedGarbage.Spec.P384

/-!
# The multiplication of a curve's base point, in its working space, as a function

**Trusted** (as every file in `Spec/`). The contract of one function for each
curve of `curves` (so far P-384), on the working space where the x86-64 code
of the curve's ECDSA signature and public key derivation keeps its numbers,
so that both can call one copy of the multiplication instead of repeating it:

* `vg_<curve>_mul_base(ws)`: `P = [k]G` (`Weierstrass.mul`, SEC 1 §2.2.1)
  for the base point `G` and the number `k` in `ws`, as a point in
  projective coordinates (`(X : Y : Z)` for `(X / Z, Y / Z)`, and
  `(0 : Y : 0)`, `Y ≠ 0`, for the point at infinity: `Represents`).

Unlike the point operations of `Spec/Weierstrass/PointOps.lean`, its result
is stated on the group: the point the coordinates stand for is `[k]G`,
however the function computes it (from tables of multiples of `G` that are
constants of the library, which it reads).

The function works in the representation of `Spec/Weierstrass/Point.lean`:
a coordinate is a number of `k` 64-bit words, little-endian, below `p`, in
Montgomery's form, standing for the element `x R⁻¹` of `GF(p)`
(`R = 2^(64 k)`, `Point.Curve.dec`), and a point is three coordinates at
consecutive offsets (`Point.Curve.pointAt`). The working space `ws` of 8192
bytes is the x86-64 code's: numbers of `k` words in slots from byte 64
(`slot`), where the code keeps the curve's prime `p` (slot 0, `modAt`), zero
(slot 3, `zeroAt`), both of which the caller provides, the result `P` (slots
14 to 16, `pAt`) and the scalar `k` (slot 31, `kAt`, any number of `k`
words). The function takes no offsets, so that every address it computes is
`ws` plus a constant. Slots 17 to 30, slot 40, the curve's temporary slot
(`tmpAt`) and the `64 k + 8` bytes from slot 45 (`bitsAt`, where the code
keeps a table of `k`'s bits) are the function's own working space (`Own`);
on return they are unspecified and may hold intermediate values, secret
ones among them, and the caller's callee-saved registers. Every other byte
of `ws` keeps its value but the result's (`Keeps`).

Everything is secret but the pointer, which is public, and the function is
constant time.
-/

namespace VG.Spec.Weierstrass.MulBase

open Mont (wsBytes)

/-- `(X : Y : Z)` stands for the point `P` in projective coordinates: the
point at infinity as `(0 : Y : 0)` for `Y ≠ 0`, and `(x, y)` as
`(x Z : y Z : Z)` for `Z ≠ 0`. -/
def Represents {W : Weierstrass.Curve} (X Y Z : Fe W) : Point W → Prop
  | .infinity => X = 0 ∧ Y ≠ 0 ∧ Z = 0
  | .affine x y => Z ≠ 0 ∧ X = x * Z ∧ Y = y * Z

/-- `ws: *mut [u64; 1024]`. -/
def sig : Sig where
  params := [("ws", .array true .u64 1024)]

/-- A curve whose base point's multiplication is a function: the curve `W`
(its group, base point and prime `p`), its name (the function is
`vg_<curve>_mul_base`, in the Rust module `<curve>_mul_base`), the count `k`
of 64-bit words of a coordinate, with `p < 2^(64 k)`, how the documentation
names it, and the slot of its products' temporary area. -/
structure Curve where
  W : Weierstrass.Curve
  curve : String
  k : Nat
  desc : String
  tmp : Nat

namespace Curve

variable (C : Curve)

/-- The curve's coordinates, as `Spec/Weierstrass/Point.lean` has them. -/
def toPoint : Point.Curve := { curve := C.curve, p := C.W.p, k := C.k, desc := C.desc }

/-- Byte offset of slot `i`: `64 + 8 k i`. -/
def slot (i : Nat) : Nat := 64 + 8 * C.k * i

/-- Where the prime `p` is. -/
def modAt : Nat := C.slot 0

/-- Where zero is. -/
def zeroAt : Nat := C.slot 3

/-- Where the result `P` is. -/
def pAt : Nat := C.slot 14

/-- Where the scalar `k` is. -/
def kAt : Nat := C.slot 31

/-- Where the table of `k`'s bits is. -/
def bitsAt : Nat := C.slot 45

/-- Where the products' temporary area is. -/
def tmpAt : Nat := C.slot C.tmp

/-- The bytes of a point. -/
def ptBytes : Nat := 24 * C.k

/-- Byte `i` is in the function's own working space: slots 17 to 30 and 40,
the temporary slot, or the `64 k + 8` bytes of the table of bits. -/
def Own (i : Nat) : Prop :=
  (C.slot 17 ≤ i ∧ i < C.slot 31) ∨ (C.slot 40 ≤ i ∧ i < C.slot 41) ∨
    (C.tmpAt ≤ i ∧ i < C.tmpAt + 8 * C.k) ∨ (C.bitsAt ≤ i ∧ i < C.bitsAt + 64 * C.k + 8)

/-- Every byte of `ws` but those of the function's own working space and of
the result keeps its value. -/
def Keeps (ws : Addr) (m m' : Mem) : Prop :=
  ∀ i < wsBytes, ¬ C.Own i → (i < C.pAt ∨ C.pAt + C.ptBytes ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

/-- The caller provides `p` at `modAt` and zero at `zeroAt`. -/
def ConstsOk (ws : Addr) (m : Mem) : Prop :=
  C.toPoint.coordAt m ws C.modAt = C.W.p ∧ C.toPoint.coordAt m ws C.zeroAt = 0

/-- The scalar `k`. -/
def scalar (ws : Addr) (m : Mem) : Nat := C.toPoint.coordAt m ws C.kAt

/-- The result: the point at `pAt` has its coordinates below `p` and stands
for `P`, and every byte of `ws` but its and the own working space's keeps
its value. -/
def Result (P : Point C.W) (ws : Addr) (m m' : Mem) : Prop :=
  let c := C.toPoint.pointAt m' ws C.pAt
  C.toPoint.Below c ∧
    Represents (W := C.W) (C.toPoint.dec c.1) (C.toPoint.dec c.2.1) (C.toPoint.dec c.2.2) P ∧
    C.Keeps ws m m'

/-- `mul_base`: `P = [k]G`. -/
def mulBaseContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A (pre := fun ws m => C.ConstsOk ws m)
    (post := fun ws m m' _ => C.Result (mul (C.scalar ws m) (G C.W)) ws m m')
    (stack := stack)

/-! ## The function -/

/-- The Rust module of the curve's function. -/
def module : String := C.curve ++ "_mul_base"

/-- Where the documentation says a range of bytes is. -/
def rangeDoc (o n : Nat) : String := s!"{o} to {o + n - 1}"

/-- What the documentation says the function's own working space is. -/
def ownDoc : String :=
  s!"Bytes {rangeDoc (C.slot 17) (C.slot 31 - C.slot 17)}, {rangeDoc (C.slot 40) (8 * C.k)}, \
    {rangeDoc C.tmpAt (8 * C.k)} and {rangeDoc C.bitsAt (64 * C.k + 8)} of `ws`"

/-- `vg_<curve>_mul_base` on every target. -/
def mulBaseApi : Api where
  module := C.module
  name := s!"vg_{C.curve}_mul_base"
  sig := sig
  contracts := some fun A stack => C.mulBaseContract A stack
  summary := s!"The multiple `P = [k]G` of {C.desc}'s base point `G`, for the number `k` of \
    {C.k} 64-bit words (`{8 * C.k}` bytes), little-endian, at byte {C.kAt} of `ws`, in projective \
    coordinates (`(X : Y : Z)` for `(X / Z, Y / Z)`, and `(0 : Y : 0)` for the point at \
    infinity) at bytes {rangeDoc C.pAt C.ptBytes}: coordinates of {C.k} 64-bit words, \
    little-endian, in Montgomery's form modulo {C.desc}'s prime `p`, below it. The function \
    reads `p` at byte {C.modAt} and zero at byte {C.zeroAt}, and tables of multiples of `G` \
    that are constants of the library. {C.ownDoc} are the function's own working space; every \
    other byte of `ws` but the result's keeps its value. Constant time: only the pointer may \
    affect timing.\n\n\
    Contract: `mulBaseContract` of `VG.Spec.Weierstrass.MulBase.Curve`."
  safety := [s!"The {C.k} words at byte {C.modAt} of `ws` must be {C.desc}'s prime `p`, and the \
      {C.k} words at byte {C.zeroAt} must be zero.",
    s!"{C.ownDoc} are unspecified on return and may hold intermediate values, which are secret \
      and which the caller must destroy."]

end Curve

/-! ## The curves -/

def p384 : Curve := { W := Spec.P384.curve, curve := "p384", k := 6, desc := "P-384", tmp := 83 }

/-- Every curve. -/
def curves : List Curve := [p384]

end VG.Spec.Weierstrass.MulBase
