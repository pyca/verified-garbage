import VerifiedGarbage.Spec.P521

/-!
# P-521's base point is on the curve

Evaluated by the kernel; it needs none of the algebra of `Curve.lean`, so the
proofs of the code can use it.
-/

namespace VG.Proof.P521

open Spec.Weierstrass

theorem onCurve_G : onCurve Spec.P521.curve (G Spec.P521.curve) = true := by
  decide +kernel

end VG.Proof.P521
