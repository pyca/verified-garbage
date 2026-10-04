import VerifiedGarbage.Proof.X448.AArch64.Base.Add
import VerifiedGarbage.Proof.X448.BaseAdd

/-!
# X448 of the base point on AArch64: the addition's environment is `addPt`

Untrusted: everything here is checked by Lean. For the two accumulators' slots,
`affEnv` puts `addPt` of the accumulator and the entry (with `Z = 1`) in the
accumulator's slots, and keeps every slot but the temporaries.
-/

namespace VG.Proof.X448.AArch64.Base

open VG.Proof.X448.AArch64.Weak (Index Env opCopy)
open VG.Spec.Ed448 (Point)
open VG.Proof.X448 (addPt)

/-- The point in slots `x`, `y`, `z`. -/
def pt (e : Env) (x y z : Index) : Point := ⟨e x, e y, e z⟩

/-- What `addAffine` computes from `(X : Y : Z)` and `(x, y)`, with `z0` (zero) in slot 19. -/
def affPt (X Y Z x y z0 : Spec.X448.Fe) : Point :=
  let b := Z * Z
  let c := X * x
  let e := Y * y
  let f := b + Spec.X448.a24 * (c * e)
  let g := b + Spec.X448.a24 * (z0 - c * e)
  ⟨Z * f * (X * y + Y * x), Z * g * (e - c), f * g⟩

theorem affEnv_A (e : Env) : pt (affEnv 0 1 2 6 7 e) 0 1 2 = affPt (e 0) (e 1) (e 2) (e 6) (e 7) (e 19) := rfl

theorem affEnv_B (e : Env) : pt (affEnv 3 4 5 8 9 e) 3 4 5 = affPt (e 3) (e 4) (e 5) (e 8) (e 9) (e 19) := rfl

theorem affPt_eq (X Y Z x y : Spec.X448.Fe) : affPt X Y Z x y 0 = addPt ⟨X, Y, Z⟩ ⟨x, y, 1⟩ := by
  simp only [affPt, addPt, Point.mk.injEq]
  refine ⟨Ed448.toZ_inj.1 ?_, Ed448.toZ_inj.1 ?_, Ed448.toZ_inj.1 ?_⟩ <;>
    simp only [Ed448.toZ_add, Ed448.toZ_sub, Ed448.toZ_mul, Ed448.toZ_zero, Ed448.toZ_one] <;> ring

end VG.Proof.X448.AArch64.Base
