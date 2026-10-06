import VerifiedGarbage.Spec.P192

/-!
# P-192's base point is on the curve

Evaluated by the kernel; it needs none of the algebra of `Curve.lean`, so the
proofs of the code can use it.
-/

namespace VG.Proof.P192

open Spec.Weierstrass

theorem onCurve_G : onCurve Spec.P192.curve (G Spec.P192.curve) = true := by
  decide +kernel

end VG.Proof.P192
