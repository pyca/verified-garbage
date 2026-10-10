import VerifiedGarbage.Proof.Ed25519.Group.Double
import VerifiedGarbage.Spec.Ed25519.Point64

/-!
# RFC 8032's doubling represents the double

`Point64.pointDouble`, RFC 8032's doubling formula (§5.1.4), is `dblPoint`
(`dbl-2008-hwcd`) with every coordinate negated (`pointDouble_neg`), the same
point: it represents `a + a` for any `X : Y : Z` representing `a`
(`pointDouble_rep`), whatever `T` is.
-/

namespace VG.Proof.Ed25519

open Spec.X25519 (Fe)
open Spec.Ed25519 (Point)
open Edwards

theorem pointDouble_neg (p : Point) :
    Spec.Ed25519.Point64.pointDouble p =
      ⟨-(dblPoint p).X, -(dblPoint p).Y, -(dblPoint p).Z, -(dblPoint p).T⟩ := by
  simp only [Spec.Ed25519.Point64.pointDouble, dblPoint]
  congr 1 <;> grind

private theorem toZ_neg' (a : Fe) : toZ (-a) = -toZ a := rfl

theorem pointDouble_rep {p : Point} {a : EPoint dZ} (h : RepP p a) :
    Rep (Spec.Ed25519.Point64.pointDouble p) (a + a) := by
  have hr := dblPoint_rep h
  rw [pointDouble_neg]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show toZ (-_) ≠ 0
    rw [toZ_neg']; exact neg_ne_zero.mpr hr.z
  · show toZ (-_) = _ * toZ (-_)
    rw [toZ_neg', toZ_neg', hr.x, mul_neg]
  · show toZ (-_) = _ * toZ (-_)
    rw [toZ_neg', toZ_neg', hr.y, mul_neg]
  · show toZ (-_) = _ * toZ (-_)
    rw [toZ_neg', toZ_neg', hr.t, mul_neg]

end VG.Proof.Ed25519
