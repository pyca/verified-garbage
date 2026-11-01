module

public import VerifiedGarbage.Impl.Weierstrass.Layout.Mul
public import VerifiedGarbage.Proof.Weierstrass.MulBaseContract

/-!
# The multiplication of a point, in a curve's working space, as an internal function

Not trusted: the contract of one function for each
curve of `curves` (so far P-192, P-224, P-256, P-384, P-521, secp256k1,
brainpoolP256r1, brainpoolP384r1 and brainpoolP512r1), on the working space where the x86-64 code of the curve's
ECDSA signature and verification, public key derivation and ECDH keeps its
numbers, so that all of them can call one copy of the multiplication instead
of repeating it:

* `vg_<curve>_mul(ws)`: `P = [k]Q` (`Weierstrass.mul`, SEC 1 §2.2.1) for the
  affine point `Q` and the number `k` in `ws`, as a point in projective
  coordinates (`MulBase.Represents`: `(X : Y : Z)` for `(X / Z, Y / Z)`, and
  `(0 : Y : 0)`, `Y ≠ 0`, for the point at infinity).

As for `Proof/Weierstrass/MulBaseContract.lean`, the result is stated on the group:
the point the coordinates stand for is `[k]Q`, however the function computes
it (the code: a ladder of complete additions, over every bit of `k`'s words).

The function works in the representation of `Proof/Weierstrass/PointContract.lean`:
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

The code of P-224, P-256, P-384 and P-521 multiplies by windows of `k`'s
digits rather than by a ladder, from a table of multiples of `Q`, with the
addition formulas for `a = -3`, which read `b R mod p` (which the function
stores itself, as `Proof/Weierstrass/PointOpsContract.lean` has it, in slot 40). For
those curves, slot 40 and every byte from slot 45 on, where each target's
code keeps its tables, its working areas and the temporary areas of its
products, are the function's own working space too (`tail`); and the result
is stated only for `k` in `[1, n - 1]`, for `n` the order of the curve's base
point (`inRange`), the scalars the windows' proofs cover (their recoding and
their Jacobian additions): for any other `k` the coordinates are
unspecified, but every byte outside the own working space and the result
keeps its value as above. A caller whose scalar may be outside that range
discards the result, or handles that scalar itself.

Everything is secret but the pointer, which is public, and the function is
constant time.

These are internal functions (`Rust.Internal`): only verified code calls them, so
only their callers' contracts, in `Spec/`, are trusted. The structures, the
layout of the working space and the curves are the code's, in
`Impl/Weierstrass/Layout/Mul.lean`; the definitions here are in their
namespaces, so that they read as fields of them.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.Mul

open VG.Spec.Weierstrass

open Mont (wsBytes)

open MulBase (Represents sig)

namespace Curve

variable (C : Curve)

/-- The scalar `k`. -/
def scalar (ws : Addr) (m : Mem) : Nat := C.toPoint.coordAt m ws C.kAt

/-- Byte `i` is in the function's own working space: slots 17 to 30, the
temporary slot, or the `64 k + 8 saved` bytes of the table of bits and the
words past it; with `tail`, also slot 40 and every byte from the table of
bits on. -/
def Own (i : Nat) : Prop :=
  (C.slot 17 ≤ i ∧ i < C.slot 31) ∨ (C.tmpAt ≤ i ∧ i < C.tmpAt + 8 * C.k) ∨
    (C.bitsAt ≤ i ∧ i < C.bitsAt + 64 * C.k + 8 * C.saved) ∨
    (C.tail = true ∧ ((C.slot 40 ≤ i ∧ i < C.slot 41) ∨ C.bitsAt ≤ i))

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

/-- The result for `k` in `[1, n - 1]`: there, `Result`'s coordinates of
`P = [k]Q`; for every `k`, its `Keeps`. -/
def ResultInRange (k : Nat) (Q : Point C.W) (ws : Addr) (m m' : Mem) : Prop :=
  let c := C.toPoint.pointAt m' ws C.pAt
  (1 ≤ k → k < C.W.n → C.toPoint.Below c ∧
    Represents (W := C.W) (C.toPoint.dec c.1) (C.toPoint.dec c.2.1) (C.toPoint.dec c.2.2) (mul k Q)) ∧
    C.Keeps ws m m'

/-- `mul` for a curve with `inRange`: `P = [k]Q` for `k` in `[1, n - 1]`. -/
def mulInRangeContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A (pre := fun ws m => C.ConstsOk ws m ∧ C.PointOk ws m)
    (post := fun ws m m' _ => C.ResultInRange (C.scalar ws m) (C.point ws m) ws m m')
    (stack := stack)

/-- The function's contract: `mulInRangeContract` with `inRange`, else
`mulContract`. -/
def contract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  if C.inRange then C.mulInRangeContract A stack else C.mulContract A stack

end Curve

end VG.Impl.Weierstrass.Mul
