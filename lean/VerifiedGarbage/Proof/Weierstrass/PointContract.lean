module

public import VerifiedGarbage.Impl.Weierstrass.Layout.Point
public import VerifiedGarbage.Proof.Weierstrass.MontContract

/-!
# Complete point addition on a curve, in Montgomery form, as internal functions

Not trusted: how two functions for a curve read its points, which the code
of a curve's functions calls instead of repeating its point addition at
every use:

* `vg_<curve>_point_add(ws)`: the sum `O = P + Q` of the points at fixed
  offsets of the working space, by the complete addition formula of Renes,
  Costello and Batina (*Complete addition formulas for prime order elliptic
  curves*, EUROCRYPT 2016, Algorithm 1);
* `vg_<curve>_point_double(ws)`: the sum `O = P + P`, by the same formula.

The functions work in the representation of `Proof/Weierstrass/MontContract.lean`:
a coordinate is a number of `k` 64-bit words, little-endian, below `p`, in
Montgomery's form, standing for the element `x R⁻¹` of `GF(p)`
(`R = 2^(64 k)`, `dec`). A point is three coordinates `X, Y, Z` (projective,
`(X : Y : Z)`) at consecutive offsets of the working space `ws` of 8192
bytes (`pointAt`). The points and the curve's constants are at fixed
offsets, just below the functions' own working space: the result `O`
(`oAt`), the operands `P` (`pAt`) and `Q` (`qAt`), and the curve's `a`
(`aAt`) and `3b` (`b3At`), in the same form, which the caller provides. The
functions take no offsets, so that every address they compute is `ws` plus
a constant. The bytes from `ownAt` to 4095 are the functions' own working
space: six coordinates for their intermediate values and 64 bytes to save
registers in (so that they need no stack for them), then the own working
space of the functions of `Proof/Weierstrass/MontContract.lean`, which they may
call. On return they are unspecified and may hold intermediate values.

P-521 is not among the curves: its points, constants and own working space,
of nine-word coordinates, would overlap the slots its code keeps in the
working space.

These are internal functions (`Rust.Internal`): only verified code calls them, so
only their callers' contracts, in `Spec/`, are trusted. The structures, the
layout of the working space and the curves are the code's, in
`Impl/Weierstrass/Layout/Point.lean`; the definitions here are in their
namespaces, so that they read as fields of them.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.Point

open Mont (wsBytes numAt)

namespace Curve

variable (C : Curve)

/-- The element of `GF(p)` that the number `x` stands for in Montgomery's
form: `x R⁻¹`, with `R⁻¹ = R^(p-2)` (Fermat's little theorem, `p` prime). -/
def dec (x : Nat) : Fin C.p :=
  Fin.ofNat C.p x * Spec.Weierstrass.pow (Fin.ofNat C.p C.R) (C.p - 2)

/-- The coordinate at offset `o` of `ws`. -/
def coordAt (m : Mem) (ws : Addr) (o : Nat) : Nat := numAt m ws (BitVec.ofNat 32 o) C.k

/-- The coordinates `X, Y, Z` of the point at offset `o`, at `o`,
`o + 8 k` and `o + 16 k`. -/
def pointAt (m : Mem) (ws : Addr) (o : Nat) : Nat × Nat × Nat :=
  (C.coordAt m ws o, C.coordAt m ws (o + elemBytes C.k), C.coordAt m ws (o + 2 * elemBytes C.k))

/-- The three coordinates of a point are below `p`. -/
def Below (P : Nat × Nat × Nat) : Prop := P.1 < C.p ∧ P.2.1 < C.p ∧ P.2.2 < C.p

end Curve

end VG.Impl.Weierstrass.Point
