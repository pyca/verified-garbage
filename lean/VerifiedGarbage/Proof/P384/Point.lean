import VerifiedGarbage.Spec.P384

/-!
# P-384's base point is on the curve

Evaluated by the kernel; it needs none of the algebra of `Curve.lean`, so the
proofs of the code can use it.
-/

namespace VG.Proof.P384

open Spec.Weierstrass

theorem onCurve_G : onCurve Spec.P384.curve (G Spec.P384.curve) = true := by
  decide +kernel

end VG.Proof.P384
