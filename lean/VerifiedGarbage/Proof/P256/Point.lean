import VerifiedGarbage.Spec.P256

/-!
# P-256's base point is on the curve

Evaluated by the kernel; it needs none of the algebra of `Curve.lean`, so the
proofs of the code can use it.
-/

namespace VG.Proof.P256

open Spec.Weierstrass

theorem onCurve_G : onCurve Spec.P256.curve (G Spec.P256.curve) = true := by
  decide +kernel

end VG.Proof.P256
