module

public import VerifiedGarbage.Impl.Weierstrass.Layout.MulBase
public import VerifiedGarbage.Proof.Weierstrass.PointContract

/-!
# The multiplication of a curve's base point, in its working space, as an internal function

Not trusted: the contract of one function for each
curve of `curves` (so far P-224, P-256, P-384 and P-521), on the working space where the x86-64 code
of the curve's ECDSA signature and public key derivation keeps its numbers,
so that both can call one copy of the multiplication instead of repeating it:

* `vg_<curve>_mul_base(ws)`: `P = [k]G` (`Weierstrass.mul`, SEC 1 §2.2.1)
  for the base point `G` and the number `k` in `ws`, as a point in
  projective coordinates (`(X : Y : Z)` for `(X / Z, Y / Z)`, and
  `(0 : Y : 0)`, `Y ≠ 0`, for the point at infinity: `Represents`).

Unlike the point operations of `Proof/Weierstrass/PointOpsContract.lean`, its result
is stated on the group: the point the coordinates stand for is `[k]G`,
however the function computes it (from tables of multiples of `G` that are
constants of the library, which it reads).

The function works in the representation of `Proof/Weierstrass/PointContract.lean`:
a coordinate is a number of `k` 64-bit words, little-endian, below `p`, in
Montgomery's form, standing for the element `x R⁻¹` of `GF(p)`
(`R = 2^(64 k)`, `Point.Curve.dec`), and a point is three coordinates at
consecutive offsets (`Point.Curve.pointAt`). The working space `ws` of 8192
bytes is the x86-64 code's: numbers of `k` words in slots from byte 64
(`slot`), where the code keeps the curve's prime `p` (slot 0, `modAt`), zero
(slot 3, `zeroAt`), both of which the caller provides, the result `P` (slots
14 to 16, `pAt`) and the scalar `k` (slot 31, `kAt`, any number of `k`
words). The function takes no offsets, so that every address it computes is
`ws` plus a constant. Slots 17 to 30, slot 40 (and slot 41 for a curve of
fewer than six words, whose slots 29 and 30 cannot hold the caller's six
callee-saved registers), the curve's temporary slot (`tmpAt`) and
the `64 k + 8` bytes from slot 45 (`bitsAt`, where the code keeps a table of
`k`'s bits) are the function's own working space (`Own`), and for a curve
with `tail` (P-521) so is every byte from slot 45 on, which holds the
temporary areas of its products modulo `p` on every target (slot 55 on
x86-64, slot 54 on AArch64);
on return they are unspecified and may hold intermediate values, secret
ones among them, and the caller's callee-saved registers. Every other byte
of `ws` keeps its value but the result's (`Keeps`).

Everything is secret but the pointer, which is public, and the function is
constant time.

These are internal functions (`Rust.Internal`): only verified code calls them, so
only their callers' contracts, in `Spec/`, are trusted. The structures, the
layout of the working space and the curves are the code's, in
`Impl/Weierstrass/Layout/MulBase.lean`; the definitions here are in their
namespaces, so that they read as fields of them.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.MulBase

open VG.Spec.Weierstrass

open Mont (wsBytes)

/-- `(X : Y : Z)` stands for the point `P` in projective coordinates: the
point at infinity as `(0 : Y : 0)` for `Y ≠ 0`, and `(x, y)` as
`(x Z : y Z : Z)` for `Z ≠ 0`. -/
def Represents {W : Spec.Weierstrass.Curve} (X Y Z : Fe W) : Point W → Prop
  | .infinity => X = 0 ∧ Y ≠ 0 ∧ Z = 0
  | .affine x y => Z ≠ 0 ∧ X = x * Z ∧ Y = y * Z

/-- `ws: *mut [u64; 1024]`. -/
def sig : Sig where
  params := [("ws", .array true .u64 1024)]

namespace Curve

variable (C : Curve)

/-- Byte `i` is in the function's own working space: slots 17 to 30 and 40
(and 41 for fewer than six words), the temporary slot, or the `64 k + 8` bytes
of the table of bits; with `tail`, also every byte from the table of bits on. -/
def Own (i : Nat) : Prop :=
  (C.slot 17 ≤ i ∧ i < C.slot 31) ∨ (C.slot 40 ≤ i ∧ i < C.slot 41) ∨
    (C.k < 6 ∧ C.slot 41 ≤ i ∧ i < C.slot 42) ∨
    (C.tmpAt ≤ i ∧ i < C.tmpAt + 8 * C.k) ∨ (C.bitsAt ≤ i ∧ i < C.bitsAt + 64 * C.k + 8) ∨
    (C.tail = true ∧ C.bitsAt ≤ i)

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

end Curve

end VG.Impl.Weierstrass.MulBase
