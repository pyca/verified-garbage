module

public import VerifiedGarbage.Spec.Weierstrass.MulBase

/-!
# The multiplication of a point, in a curve's working space, as a function

**Trusted** (as every file in `Spec/`). The contract of one function for each
curve of `curves` (so far P-192, secp256k1, brainpoolP256r1,
brainpoolP384r1 and brainpoolP512r1), on the working space where the x86-64 code of the curve's
ECDSA signature and verification, public key derivation and ECDH keeps its
numbers, so that all of them can call one copy of the multiplication instead
of repeating it:

* `vg_<curve>_mul(ws)`: `P = [k]Q` (`Weierstrass.mul`, SEC 1 §2.2.1) for the
  affine point `Q` and the number `k` in `ws`, as a point in projective
  coordinates (`MulBase.Represents`: `(X : Y : Z)` for `(X / Z, Y / Z)`, and
  `(0 : Y : 0)`, `Y ≠ 0`, for the point at infinity).

As for `Spec/Weierstrass/MulBase.lean`, the result is stated on the group:
the point the coordinates stand for is `[k]Q`, however the function computes
it (the code: a ladder of complete additions, over every bit of `k`'s words).

The function works in the representation of `Spec/Weierstrass/Point.lean`:
a coordinate is a number of `k` 64-bit words, little-endian, below `p`, in
Montgomery's form, standing for the element `x R⁻¹` of `GF(p)`
(`R = 2^(64 k)`, `Point.Curve.dec`). The working space `ws` of 8192 bytes is
the x86-64 code's: numbers of `k` words in slots from byte 64 (`slot`). The
caller provides the curve's prime `p` (slot 0, `modAt`), zero (slot 3,
`zeroAt`), and in Montgomery's form one, the coefficient `a` and `3 b`
(slots 5 to 7, `oneAt`, `aAt`, `b3At`), the constants of the complete
addition formulas, which the function reads from `ws` rather than holding
them in its code; the point `Q`, as its affine coordinates in Montgomery's
form, below `p`, on the curve, in the first two slots of the result (slots
14 and 15, `qAt`); and the scalar `k` (slot 31, `kAt`, any number of `k`
words). The result `P` replaces `Q`, in slots 14 to 16 (`pAt`). The
function takes no offsets, so that every address it computes is `ws` plus a
constant. Slots 17 to 30 (where the code keeps, among others, its copy of
`Q`), the curve's temporary slot (`tmpAt`) and the `64 k + 8 s` bytes from
slot 45 (`bitsAt`, where the code keeps a table of `k`'s bits, then in `s`
words, `saved`, the callee-saved registers it changes: one, but six for
brainpoolP512r1, whose products of eight words change more of them on
AArch64) are the function's own working space (`Own`); on return they are unspecified and may
hold intermediate values, secret ones among them. Every other byte of `ws`
keeps its value but the result's (`Keeps`).

Everything is secret but the pointer, which is public, and the function is
constant time.
-/

@[expose] public section

namespace VG.Spec.Weierstrass.Mul

open Mont (wsBytes)
open MulBase (Represents sig)

/-- A curve whose points' multiplication is a function: the curve `W` (its
group and prime `p`), its name (the function is `vg_<curve>_mul`, in the
Rust module `<curve>_mul`), the count `k` of 64-bit words of a coordinate,
with `p < 2^(64 k)`, how the documentation names it, the slot of its
products' temporary area, and the count of words past the table of bits
where the function may keep the callee-saved registers it changes. -/
structure Curve where
  W : Weierstrass.Curve
  curve : String
  k : Nat
  desc : String
  tmp : Nat
  saved : Nat := 1

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

/-- The scalar `k`. -/
def scalar (ws : Addr) (m : Mem) : Nat := C.toPoint.coordAt m ws C.kAt

/-- Where the documentation says a range of bytes is. -/
def rangeDoc (o n : Nat) : String := s!"{o} to {o + n - 1}"

/-- Where one (`R mod p`) is. -/
def oneAt : Nat := C.slot 5

/-- Where `a R mod p` is. -/
def aAt : Nat := C.slot 6

/-- Where `3 b R mod p` is. -/
def b3At : Nat := C.slot 7

/-- Where the point `Q` is: its affine coordinates, `x` then `y`, where the
result goes. -/
def qAt : Nat := C.pAt

/-- `x R mod p`: the Montgomery form of `x`. -/
def mont (x : Nat) : Nat := x * 2 ^ (64 * C.k) % C.W.p

/-- Byte `i` is in the function's own working space: slots 17 to 30, the
temporary slot, or the `64 k + 8 saved` bytes of the table of bits and the
words past it. -/
def Own (i : Nat) : Prop :=
  (C.slot 17 ≤ i ∧ i < C.slot 31) ∨ (C.tmpAt ≤ i ∧ i < C.tmpAt + 8 * C.k) ∨
    (C.bitsAt ≤ i ∧ i < C.bitsAt + 64 * C.k + 8 * C.saved)

/-- Every byte of `ws` but those of the function's own working space and of
the result keeps its value. -/
def Keeps (ws : Addr) (m m' : Mem) : Prop :=
  ∀ i < wsBytes, ¬ C.Own i → (i < C.pAt ∨ C.pAt + C.ptBytes ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

/-- The caller provides `p`, zero, and one, `a` and `3 b` in Montgomery's
form. -/
def ConstsOk (ws : Addr) (m : Mem) : Prop :=
  C.toPoint.coordAt m ws C.modAt = C.W.p ∧ C.toPoint.coordAt m ws C.zeroAt = 0 ∧
    C.toPoint.coordAt m ws C.oneAt = C.mont 1 ∧ C.toPoint.coordAt m ws C.aAt = C.mont C.W.a ∧
    C.toPoint.coordAt m ws C.b3At = C.mont (3 * C.W.b)

/-- The affine coordinates at `qAt`. -/
def qCoords (ws : Addr) (m : Mem) : Nat × Nat :=
  (C.toPoint.coordAt m ws C.qAt, C.toPoint.coordAt m ws (C.qAt + 8 * C.k))

/-- The point `Q` the coordinates stand for. -/
def point (ws : Addr) (m : Mem) : Point C.W :=
  .affine (C.toPoint.dec (C.qCoords ws m).1) (C.toPoint.dec (C.qCoords ws m).2)

/-- The caller provides `Q`: coordinates below `p`, of a point on the curve. -/
def PointOk (ws : Addr) (m : Mem) : Prop :=
  (C.qCoords ws m).1 < C.W.p ∧ (C.qCoords ws m).2 < C.W.p ∧ onCurve C.W (C.point ws m) = true

/-- The result: the point at `pAt` has its coordinates below `p` and stands
for `P`, and every byte of `ws` but its and the own working space's keeps
its value. -/
def Result (P : Point C.W) (ws : Addr) (m m' : Mem) : Prop :=
  let c := C.toPoint.pointAt m' ws C.pAt
  C.toPoint.Below c ∧
    Represents (W := C.W) (C.toPoint.dec c.1) (C.toPoint.dec c.2.1) (C.toPoint.dec c.2.2) P ∧
    C.Keeps ws m m'

/-- `mul`: `P = [k]Q`. -/
def mulContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A (pre := fun ws m => C.ConstsOk ws m ∧ C.PointOk ws m)
    (post := fun ws m m' _ => C.Result (mul (C.scalar ws m) (C.point ws m)) ws m m')
    (stack := stack)

/-! ## The function -/

/-- The Rust module of the curve's function. -/
def module : String := C.curve ++ "_mul"

/-- What the documentation says the function's own working space is. -/
def ownDoc : String :=
  s!"Bytes {rangeDoc (C.slot 17) (C.slot 31 - C.slot 17)}, \
    {rangeDoc C.tmpAt (8 * C.k)} and {rangeDoc C.bitsAt (64 * C.k + 8 * C.saved)} of `ws`"

/-- `vg_<curve>_mul` on every target. -/
def mulApi : Api where
  module := C.module
  name := s!"vg_{C.curve}_mul"
  sig := sig
  contracts := some fun A stack => C.mulContract A stack
  summary := s!"The multiple `P = [k]Q` of a point `Q` of {C.desc}, for the number `k` of {C.k} \
    64-bit words (`{8 * C.k}` bytes), little-endian, at byte {C.kAt} of `ws`, and `Q`'s affine \
    coordinates `x` and `y` at bytes {C.qAt} and {C.qAt + 8 * C.k}, in projective coordinates \
    (`(X : Y : Z)` for `(X / Z, Y / Z)`, and `(0 : Y : 0)` for the point at infinity) in \
    `Q`'s place, at bytes {rangeDoc C.pAt C.ptBytes}: coordinates of {C.k} 64-bit words, little-endian, in \
    Montgomery's form modulo {C.desc}'s prime `p`, below it. The function reads `p` at byte \
    {C.modAt}, zero at byte {C.zeroAt}, and one, `a` and `3 b` in Montgomery's form at bytes \
    {C.oneAt}, {C.aAt} and {C.b3At}. {C.ownDoc} are the function's own working space; every other \
    byte of `ws` but the result's keeps its value. Constant time: only the pointer may affect \
    timing.\n\n\
    Contract: `mulContract` of `VG.Spec.Weierstrass.Mul.Curve`."
  safety := [s!"The {C.k} words at byte {C.modAt} of `ws` must be {C.desc}'s prime `p`, the \
      {C.k} words at byte {C.zeroAt} zero, and those at bytes {C.oneAt}, {C.aAt} and {C.b3At} \
      `R mod p`, `a R mod p` and `3 b R mod p`, for `R = 2^{64 * C.k}`.",
    s!"The {C.k} words at bytes {C.qAt} and {C.qAt + 8 * C.k} of `ws` must be below `p`, and \
      stand (in Montgomery's form) for the coordinates of a point on the curve.",
    s!"{C.ownDoc} are unspecified on return and may hold intermediate values, which are secret \
      and which the caller must destroy."]

end Curve

/-! ## The curves -/

def p192 : Curve := { W := Spec.P192.curve, curve := "p192", k := 4, desc := "P-192", tmp := 2 }
def secp256k1 : Curve :=
  { W := Spec.Secp256k1.curve, curve := "secp256k1", k := 4, desc := "secp256k1", tmp := 2 }
def brainpoolp256r1 : Curve :=
  { W := Spec.BrainpoolP256r1.curve, curve := "brainpoolp256r1", k := 4, desc := "brainpoolP256r1",
    tmp := 2 }

/-- brainpoolP384r1's temporary area is in slot 83's place, as P-384's is for six
words (`Impl.Ecdsa.X86_64.Cfg.sl`). -/
def brainpoolp384r1 : Curve :=
  { W := Spec.BrainpoolP384r1.curve, curve := "brainpoolp384r1", k := 6, desc := "brainpoolP384r1",
    tmp := 83 }

def brainpoolp512r1 : Curve :=
  { W := Spec.BrainpoolP512r1.curve, curve := "brainpoolp512r1", k := 8, desc := "brainpoolP512r1",
    tmp := 2, saved := 6 }

/-- Every curve. -/
def curves : List Curve := [p192, secp256k1, brainpoolp256r1, brainpoolp384r1, brainpoolp512r1]

end VG.Spec.Weierstrass.Mul
