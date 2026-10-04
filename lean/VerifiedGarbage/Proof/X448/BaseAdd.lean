import VerifiedGarbage.Proof.Ed448.Group.Projective
import VerifiedGarbage.Proof.X448.Edwards.Ladder

/-!
# The fixed-base comb's addition is the specification's

`addPt`: RFC 8032 §5.2.4's addition as the comb computes it (with
`Impl/X448/AArch64/Base.lean`'s field operations): `b ∓ d·c·e` as
`b + 39081 (c e)` and `b + 39081 (0 - c e)` (`d = -39081 = -a24`), and
`h - c - e` as `X₁Y₂ + Y₁X₂`. It is the specification's `pointAdd`
(`addPt_eq`), so it represents the sum of the points represented.
-/

namespace VG.Proof.X448

open VG.Spec.Ed448 VG.Proof.Ed448 VG.Proof.EdwardsLaw
open Spec.X448 (Fe a24)

/-- The comb's addition of `p` and `q`. -/
def addPt (p q : Point) : Point :=
  let a := p.Z * q.Z
  let b := a * a
  let c := p.X * q.X
  let e := p.Y * q.Y
  let f := b + a24 * (c * e)
  let g := b + a24 * (0 - c * e)
  let k := p.X * q.Y + p.Y * q.X
  ⟨a * f * k, a * g * (e - c), f * g⟩

theorem addPt_eq (p q : Point) : addPt p q = pointAdd p q := by
  have hd : Spec.Ed448.d = 0 - a24 := rfl
  simp only [addPt, pointAdd, hd, Point.mk.injEq]
  refine ⟨Ed448.toZ_inj.1 ?_, Ed448.toZ_inj.1 ?_, Ed448.toZ_inj.1 ?_⟩ <;>
    simp only [toZ_add, toZ_sub, toZ_mul, toZ_zero] <;> ring

theorem addPt_rep {p q : Point} {a b : EPoint dZ} (hp : Rep p a) (hq : Rep q b) :
    Rep (addPt p q) (a + b) := by
  rw [addPt_eq]; exact pointAdd_rep hp hq

/-- The u-coordinate `Y² / X²` (`(X²)^(p-2) = 0` for `X = 0`) of a representative is
`y² / x²` of the point represented. -/
theorem u_rep {p : Point} {a : EPoint dZ} (h : Rep p a) :
    Ed448.toZ (p.Y * p.Y * Spec.X448.pow (p.X * p.X) (Spec.X448.P - 2)) = a.y ^ 2 / a.x ^ 2 := by
  rw [toZ_mul, toZ_mul, toZ_pow, toZ_mul, Edwards.pow_P_sub_two, h.x, h.y]
  have hz := h.z
  by_cases hx : a.x = 0
  · simp [hx]
  · field_simp

end VG.Proof.X448
