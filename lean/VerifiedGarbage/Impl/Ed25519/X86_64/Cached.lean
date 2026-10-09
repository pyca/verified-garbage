import VerifiedGarbage.Impl.Ed25519.X86_64.PointMul

/-!
# Cached points

A cached point `[Y - X, Y + X, 2dT, 2Z]` of `q` is added to the accumulator
with eight multiplications (`pointAddCached`); constant cached points are
written to a table from immediates (`cachedPointStore`).
-/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64

/-- Add the cached point in slots 4–7 (`[Y - X, Y + X, 2dT, 2Z]` of `q`) to
the point in slots 0–3: the specification's `pointAdd p q`, in place.
Slots 8–15 are temporary. -/
def pointAddCachedOps : List FieldOp := [
  .sub 8 1 0, .mul 8 8 4,
  .add 9 1 0, .mul 9 9 5,
  .mul 10 3 6, .mul 11 2 7,
  .sub 12 9 8, .sub 13 11 10, .add 14 11 10, .add 15 9 8,
  .mul 0 12 13, .mul 1 14 15, .mul 2 13 14, .mul 3 12 15]

def pointAddCached (fld : Arith) : List Instr := fieldCode fld pointAddCachedOps

/-- Add the affine cached point in slots 4–6 (`[Y - X, Y + X, 2dT]` of `q`, with `Z = 1`)
to the point in slots 0–3: `pointAddCachedOps` with `2Z = 2`, whose product with `Z₁` is
`Z₁ + Z₁`. Slots 8–15 are temporary.

The operations are ordered by their dependencies rather than by the formula:
each sum or difference is computed at least two operations before the
multiplication that reads it, so the processor is not waiting for the
addition's carry chain to reach memory when a multiplication starts, and the
independent multiplications stand next to each other.

The sums and differences are folded once (`fieldCodeL`): the subtrahend of each
difference, and an operand of each sum, is a product or a coordinate of the
accumulator, which is a product too, and so at most `2p`. -/
def pointAddAffineOps : List FieldOp := [
  .sub 8 1 0, .add 9 1 0, .add 11 2 2,
  .mul 10 3 6, .mul 8 8 4, .mul 9 9 5,
  .sub 12 9 8, .add 15 9 8, .sub 13 11 10, .add 14 11 10,
  .mul 0 12 13, .mul 3 12 15, .mul 1 14 15, .mul 2 13 14]

def pointAddAffine (fld : Arith) : List Instr := fieldCodeL fld pointAddAffineOps

/-- A field constant to byte `dst` from `rax`. -/
def cachedFieldStore (v : Spec.X25519.Fe) (dst : Nat) : List Instr := constWords v ++ tableWords dst

/-- A cached point to the table entry at byte `dst` from `rax`. -/
def cachedPointStore (q : Spec.Ed25519.Point) (dst : Nat) : List Instr :=
  cachedFieldStore q.X dst ++ (cachedFieldStore q.Y (dst + 32) ++
    (cachedFieldStore q.Z (dst + 64) ++ cachedFieldStore q.T (dst + 96)))

end VG.Impl.Ed25519.X86_64
